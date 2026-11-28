'use strict';

const assert = require('node:assert');
const { Validator } = require('..');
const { toStandaloneModule } = require('../build');
const { multipleOfOk, decimalDivisor, multipleOfFast } = require('../lib/multiple-of');
const { compileToJS, compileToJSCodegenWithErrors, compileToJSCombined } = require('../lib/js-compiler');
const { compileVerdict } = require('../lib/plan-source');

const EXPECTED_CHECKS = 21089;
// Every assert goes through check(), so the final count shows the test ran
// the checks it names and did not pass by doing nothing.
let checks = 0;
const check = (actual, expected, message) => { checks++; assert.strictEqual(actual, expected, message); };

const CASES = [
  [1e20, 3, false],
  [3e20, 3, true],
  [1e308, 0.5, true],
  [-1e308, 0.5, true],
  [1e308, 0.123456789, false],
  [0.30000000000000004, 0.1, false],
  [0.3, 0.1, true],
  [0.0075, 0.0001, true],
  [0.00751, 0.0001, false],
  [4e-8, 1e-8, true],
  [1.5e-8, 1e-8, false],
  [0, 0.1, true],
  [-0, 0.1, true],
  [1, 0.1, true],
  [1, 0.3, false],
  [9007199254740992, 2, true],
  [9007199254740992, 3, false],
  [1e-300, 1e-300, true],
  [1e-300, 3e-300, false],
  [6e-300, 3e-300, true],
  [5e-324, 5e-324, true],
  [1e-323, 5e-324, true],
  [1e21, 7, false],
  [7e21, 7, true],
  [10, 0, false],
  [NaN, 1, false],
];

for (const [value, divisor, expected] of CASES) {
  check(multipleOfOk(value, divisor), expected, `direct multipleOfOk(${value}, ${divisor})`);
  if (!Number.isFinite(value) || divisor === 0) continue;
  for (const schema of [{ multipleOf: divisor }, { type: 'number', multipleOf: divisor }, { type: 'object', properties: { n: { type: 'number', multipleOf: divisor } }, required: ['n'] }]) {
    const doc = schema.properties ? { n: value } : value;
    const cg = new Validator(schema);
    const ip = new Validator(schema, { engine: 'interpreter' });
    check(cg.validate(doc).valid, expected, `codegen ${JSON.stringify(schema)} on ${value}`);
    check(cg.isValidObject(doc), expected, `isValidObject ${JSON.stringify(schema)} on ${value}`);
    check(ip.validate(doc).valid, expected, `interpreter ${JSON.stringify(schema)} on ${value}`);
    const m = { exports: {} };
    new Function('module', 'exports', toStandaloneModule(schema, { format: 'cjs' }))(m, m.exports);
    check(m.exports.isValid(doc), expected, `standalone ${JSON.stringify(schema)} on ${value}`);
  }
}

// decimalDivisor splits a divisor once into P = 10^k and an integer M, or
// returns null when the fast path does not apply.
const pairOf = (m) => { const r = decimalDivisor(m); return r === null ? null : `${r.P}/${r.M}`; };
check(pairOf(0.01), '100/1', 'decimalDivisor(0.01)');
check(pairOf(1.5), '10/15', 'decimalDivisor(1.5)');
check(pairOf(2.5), '10/25', 'decimalDivisor(2.5)');
check(pairOf(1e-7), '10000000/1', 'decimalDivisor(1e-7)');
check(pairOf(0.5), '10/5', 'decimalDivisor(0.5)');
check(pairOf(1e-15), '1000000000000000/1', 'decimalDivisor(1e-15)');
// An integer divisor has no fast path: multipleOfOk answers two safe
// integers with one %.
for (const m of [3, 5, 1000000, 0, -0, NaN, Infinity, -Infinity, 1e-16, 0.0000000000000001, 1e21, 1234567890123456, 0.1234567890123456]) {
  check(pairOf(m), null, `decimalDivisor(${m}) has no fast path`);
}

// The bound of multipleOfFast is 1e15, not 2^53: past 1e15 the round trip
// through the scaled integer loses the value.
check(Math.round(38976600501045.13 * 100) / 100 === 38976600501045.13, false, 'round trip past 1e15 fails');
check(multipleOfOk(38976600501045.13, 0.01), true, '38976600501045.13 is a multiple of 0.01');

// Differential: multipleOfFast with the decimalDivisor pair against
// multipleOfOk, on fixed and seeded pseudo-random values. The integer
// divisors 3 and 5 have no pair, so their values go through the engines
// instead (generated code, the interpreter, the closure compiler and
// plan-source), each against multipleOfOk.
const FAST_DIVISORS = [0.01, 0.1, 0.5, 0.25, 0.05, 0.001, 0.0001, 0.03, 0.07, 1.5, 2.5, 0.125, 3, 5, 1e-7, 3e-7, 1e-9, 2e-9, 1e-12, 1e-15, 7e-15];
const ulpBuf = new DataView(new ArrayBuffer(8));
const ulpStep = (x, steps) => {
  if (!Number.isFinite(x)) return x;
  let v = x;
  for (let i = 0; i < Math.abs(steps); i++) {
    if (v === 0) { v = steps > 0 ? 5e-324 : -5e-324; continue; }
    ulpBuf.setFloat64(0, v);
    const bits = ulpBuf.getBigUint64(0);
    const away = (v > 0) === (steps > 0);
    ulpBuf.setBigUint64(0, away ? bits + 1n : bits - 1n);
    v = ulpBuf.getFloat64(0);
  }
  return v;
};
const withNeighbours = (x) => [x, ulpStep(x, 1), ulpStep(x, 2), ulpStep(x, -1), ulpStep(x, -2)];
let dseed = 0x9e3779b9;
const dnext = () => { dseed = (Math.imul(dseed, 1664525) + 1013904223) >>> 0; return dseed; };
let fastAcceptsExactRejects = 0;
let fastRejectsExactAccepts = 0;
const acceptDiffs = [];
const rejectDiffs = [];
// One answer for d from every engine, or 'engines differ' when they do not
// agree, which is counted with the accepting direction below so it cannot
// pass unnoticed.
const integerEngines = (m) => {
  const schema = { type: 'number', multipleOf: m };
  const cg = new Validator(schema);
  for (let i = 0; i < 5; i++) cg.isValidObject(m);
  const ip = new Validator(schema, { engine: 'interpreter' });
  const closure = compileToJS(schema);
  const verdict = compileVerdict(schema, {});
  assert.ok(verdict !== null, `plan-source compiles ${JSON.stringify(schema)}`);
  return (d) => {
    const answers = [cg.isValidObject(d), cg.validate(d).valid, ip.isValidObject(d), ip.validate(d).valid, closure(d), verdict.fn(d)];
    return answers.every((a) => a === answers[0]) ? answers[0] : 'engines differ';
  };
};
for (const m of FAST_DIVISORS) {
  const split = decimalDivisor(m);
  assert.ok(split !== null || Number.isInteger(m), `decimalDivisor(${m}) has a fast path`);
  const pair = split !== null ? split : { P: 1, M: m };
  const answer = split !== null ? (d) => multipleOfFast(d, m, pair.P, pair.M) : integerEngines(m);
  const values = [0, -0, NaN, Infinity, -Infinity, 1e20, -1e20, 1e308, -1e308, 38976600501045.13, 80000000000000.1, 1234567890123456.7, 0.1234567890123456, 9.999999999999999, 123.4567890123456];
  for (const s of [1e15 - 1, 1e15, 1e15 + 1]) for (const sign of [1, -1]) values.push(...withNeighbours(sign * s / pair.P), sign * Number(`${s}e-${Math.log10(pair.P)}`));
  for (let i = 0; i < 300; i++) values.push(...withNeighbours((1 + (dnext() % 9999999)) / 100));
  for (let e = -16; e <= 22; e++) for (let i = 0; i < 4; i++) values.push(...withNeighbours(Number(`${pair.M * ((dnext() % 99999) + 1)}e${e - Math.log10(pair.P)}`)));
  for (let i = 0; i < 600; i++) {
    const digits = String(1000000000000000 + (dnext() % 900000000) * 10000000 + (dnext() % 10000000));
    const point = dnext() % 17;
    values.push(Number(`${dnext() % 2 ? '-' : ''}${digits.slice(0, point)}.${digits.slice(point)}`));
  }
  for (const d of values) {
    const fast = answer(d);
    const exact = multipleOfOk(d, m);
    if (fast === exact) continue;
    const diffs = fast !== false ? acceptDiffs : rejectDiffs;
    if (fast !== false) fastAcceptsExactRejects++; else fastRejectsExactAccepts++;
    if (diffs.length < 5) diffs.push(`${d} % ${m}`);
  }
}
check(fastAcceptsExactRejects, 0, `fast path ACCEPTS values the exact rule rejects (silent acceptance): ${acceptDiffs.join('; ')}`);
check(fastRejectsExactAccepts, 0, `fast path rejects values the exact rule accepts: ${rejectDiffs.join('; ')}`);

// Fixed cases for the fast path through every engine: a value past 1e15 when
// scaled, a divisor with 16 fractional digits that falls back, and an
// exponent-form divisor.
const FAST_CASES = [
  [38976600501045.13, 0.01, true],
  [80000000000000.1, 0.05, multipleOfOk(80000000000000.1, 0.05)],
  [3e-16, 0.0000000000000001, true],
  [3.5e-16, 0.0000000000000001, false],
  [3e-7, 1e-7, true],
  [3.5e-7, 1e-7, false],
  [19.99, 0.01, true],
  [19.995, 0.01, false],
  [2.5, 5, false],
  [-0, 5, true],
  [10, 5, true],
  [-15, 5, true],
  [9007199254740992, 2, true],
  [9007199254740992, 3, false],
];
check(FAST_CASES[1][2], true, '80000000000000.1 is a multiple of 0.05 by the exact rule');
const COMBINED_VALID = Object.freeze({ valid: true, errors: Object.freeze([]) });
for (const [value, divisor, expected] of FAST_CASES) {
  check(multipleOfOk(value, divisor), expected, `direct multipleOfOk(${value}, ${divisor})`);
  for (const schema of [{ multipleOf: divisor }, { type: 'number', multipleOf: divisor }, { type: 'object', properties: { n: { type: 'number', multipleOf: divisor } }, required: ['n'] }]) {
    const doc = schema.properties ? { n: value } : value;
    const label = `${JSON.stringify(schema)} on ${value}`;
    check(new Validator(schema).isValidObject(doc), expected, `isValidObject first call (tier 0) ${label}`);
    const cg = new Validator(schema);
    const ip = new Validator(schema, { engine: 'interpreter' });
    check(cg.validate(doc).valid, expected, `codegen ${label}`);
    check(cg.isValidObject(doc), expected, `isValidObject ${label}`);
    for (let i = 0; i < 3; i++) cg.isValidObject(doc);
    check(cg.isValidObject(doc), expected, `isValidObject after tier 0 ${label}`);
    check(ip.validate(doc).valid, expected, `interpreter ${label}`);
    check(ip.isValidObject(doc), expected, `interpreter isValidObject ${label}`);
    check(compileToJS(schema)(doc), expected, `closure compiler ${label}`);
    const verdict = compileVerdict(schema, {});
    assert.ok(verdict !== null, `plan-source compiles ${label}`);
    check(verdict.fn(doc), expected, `plan-source ${label}`);
    const withErrors = compileToJSCodegenWithErrors(schema)(doc);
    check(withErrors.valid, expected, `codegen with errors ${label}`);
    check(withErrors.valid || withErrors.errors[0].keyword === 'multipleOf', true, `codegen with errors names multipleOf ${label}`);
    const combined = compileToJSCombined(schema, COMBINED_VALID)(doc);
    check(combined.valid, expected, `combined ${label}`);
    check(combined.valid || combined.errors[0].keyword === 'multipleOf', true, `combined names multipleOf ${label}`);
    const m = { exports: {} };
    new Function('module', 'exports', toStandaloneModule(schema, { format: 'cjs' }))(m, m.exports);
    check(m.exports.isValid(doc), expected, `standalone ${label}`);
  }
}

// Independent decimal reference over 20,000 pseudo-random pairs.
let seed = 0x1234567;
const next = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed; };
const toRat = (x) => {
  const m = /^(\d+)(?:\.(\d+))?(?:e([+-]\d+))?$/.exec(String(Math.abs(x)));
  const frac = m[2] || '';
  const exp = (m[3] ? Number(m[3]) : 0) - frac.length;
  return [BigInt(m[1] + frac), exp];
};
const refOk = (d, m) => {
  if (!Number.isFinite(d) || !Number.isFinite(m) || m === 0) return false;
  const [da, ea] = toRat(d), [db, eb] = toRat(m);
  const k = Math.min(ea, eb);
  return (da * 10n ** BigInt(ea - k)) % (db * 10n ** BigInt(eb - k)) === 0n;
};

for (let i = 0; i < 20000; i++) {
  const mode = next() % 4;
  let d, m;
  if (mode === 0) {
    m = (next() % 1000) + 1;
    d = (next() % 2 === 0 ? m * (next() % 100000) : (next() % 1000000)) * (next() % 2 ? 1 : -1);
  } else if (mode === 1) {
    const exp = (next() % 40) - 20;
    m = Number(`${(next() % 99) + 1}e${exp}`);
    d = Number(`${(next() % 9999) + 1}e${exp + (next() % 5) - 2}`);
  } else if (mode === 2) {
    m = Number(`${(next() % 9) + 1}e${(next() % 10) - 5}`);
    d = Number(`${(next() % 9) + 1}e${20 + (next() % 280)}`);
  } else {
    const buf = new ArrayBuffer(8);
    const u32 = new Uint32Array(buf);
    const f64 = new Float64Array(buf);
    u32[0] = next(); u32[1] = next();
    d = f64[0];
    u32[0] = next(); u32[1] = next();
    m = f64[0];
  }
  if (!Number.isFinite(d) || !Number.isFinite(m) || m === 0) continue;
  checks++;
  assert.strictEqual(multipleOfOk(d, m), refOk(d, m), `random pair (${d}, ${m})`);
}

// The standalone module a schema with multipleOf builds still imports nothing:
// the helper is written into it.
for (const format of ['cjs', 'esm']) {
  const src = toStandaloneModule({ type: 'number', multipleOf: 0.1 }, { format });
  check(/\brequire\(|^\s*import\b/m.test(src), false, `standalone ${format} module imports nothing`);
}

// ata-validator/kernels and the backends of ata-validator/ir. The closure
// backend and the kernel module reach no CommonJS file, so they carry their own
// copy of lib/multiple-of.js (lib/kernels/multiple-of.mjs); these runs hold the
// copies to the same answers. Values from the review: 1e20 for 3 and
// 0.30000000000000004 for 0.1 are not multiples, 1e308 for 0.5 is.
async function backends() {
  const { closureModule } = await import('../lib/ir/closures.mjs');
  const { specialize, functionBody } = await import('../lib/ir/emit.mjs');
  const K = await import('../lib/kernels/index.mjs');
  const loadClosure = (src) => {
    const m = /^import \{([^}]*)\} from "[^"\n]*"\n/.exec(src);
    assert.ok(m, 'closure module starts with its import');
    return new Function('K', `const {${m[1]}}=K\n` + src.slice(m[0].length).replace(/^export const\{isValid,validate\}=/m, 'const{isValid,validate}=') + 'return{isValid,validate}')(K);
  };
  const loadEmitted = (src) => new Function('K', functionBody(src))(K);
  for (const [value, divisor, expected] of [...CASES, ...FAST_CASES]) {
    if (!Number.isFinite(value) || divisor === 0) continue;
    const schema = { multipleOf: divisor };
    check(K.mok(value, divisor), expected, `kernels mok(${value}, ${divisor})`);
    const c = closureModule(schema, { richErrors: false, useDefaults: false });
    assert.ok(c !== null, 'closureModule takes {multipleOf}');
    const closure = loadClosure(c);
    check(closure.isValid(value), expected, `closure isValid ${value} % ${divisor}`);
    check(closure.validate(value).valid, expected, `closure validate ${value} % ${divisor}`);
    for (const richErrors of [false, true]) {
      const emitted = loadEmitted(specialize(schema, { verdict: true, richErrors, useDefaults: false }));
      check(emitted.isValid(value), expected, `emitted module (richErrors ${richErrors}) ${value} % ${divisor}`);
    }
  }
}

backends().then(() => {
  assert.strictEqual(checks, EXPECTED_CHECKS, `expected ${EXPECTED_CHECKS} checks, ran ${checks}`);
  console.log(`ok: exact decimal multipleOf matches across engines, the closure backend, the kernels and 20000 random pairs (${checks} checks)`);
}, (e) => { console.error(e); process.exit(1); });

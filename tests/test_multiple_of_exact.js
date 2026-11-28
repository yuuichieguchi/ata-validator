'use strict';

const assert = require('node:assert');
const { Validator } = require('..');
const { toStandaloneModule } = require('../build');
const { multipleOfOk, decimalDivisor, multipleOfFast, multipleOfInteger } = require('../lib/multiple-of');
const { compileToJS, compileToJSCodegenWithErrors, compileToJSCombined } = require('../lib/js-compiler');
const { compileVerdict } = require('../lib/plan-source');

const EXPECTED_CHECKS = 21149;
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

// Integer divisors through every engine, on every call: tier 0 answering
// every call (engine: 'interpreter'), the first calls of a default validator,
// generated code after them, the interpreted walk and the closure tree of a
// schema tier 0 does not take, the closure compiler, plan-source, the two
// error generators and a standalone module. The values include integers
// above 2^31 and near 2^53, where a remainder or a quotient test can go wrong,
// and values above 2^53, which take the exact decimal reading.
// The reference: for two safe integers (divisor not 0) it is BigInt
// remainder, which shares no code with lib/multiple-of.js, so a wrong
// quotient test there cannot pass by agreeing with itself; multipleOfOk and
// multipleOfInteger are held to it like the engines. For any other value
// (fractions, values above 2^53) it is multipleOfOk, whose decimal reading
// the random pairs further down check against an independent BigInt reading.
const INT_DIVISORS = [1, 2, 3, 5, 7, 1000, 2 ** 31, 2 ** 31 + 1, 3e15, 2 ** 53 - 1, -1, -3, -1000, -(2 ** 53 - 1)];
const intValues = (m) => {
  const out = [0, -0, 1, -1, 2, 3, 4, 5, 6, 7, 10, 14, 15, 999, 1000, 1001, 2.5, -2.5, 0.5, 1e-300, 5e-324, 7.000000000000001, 1000.0000000000001, NaN, Infinity, -Infinity];
  for (const x of [2 ** 31 - 1, 2 ** 31, 2 ** 31 + 1, 2 ** 32, 1.7e12, 1700000000000, 1700000000001, 2 ** 53 - 1, 2 ** 53 - 2, 2 ** 53 - 3, 2 ** 52, 2 ** 52 + 1, 3e15, 6e15, 9e15]) out.push(x, -x, x + 1, x - 1);
  for (const x of [2 ** 53, 2 ** 53 + 2, 2 ** 54, 1e20, 3e20, 1e21, 7e21, 1e308]) out.push(...withNeighbours(x), -x);
  const a = Math.abs(m);
  for (const k of [1, 2, 3, 7, 1000, 4096, 1e6]) { const x = a * k; out.push(x, -x, x + 1, x - 1); }
  for (const k of [Math.floor((2 ** 53 - 1) / a), Math.floor((2 ** 53 - 1) / a) - 1]) { const x = a * k; out.push(x, -x, x + 1, x - 1); }
  for (let i = 0; i < 40; i++) { const x = a * ((dnext() % 1000000) + 1); out.push(x, x + (dnext() % 3) - 1); }
  return out;
};
const NOT_TIER0 = (schema) => ({ ...schema, not: { const: 0.123 } });
let intAcceptsExactRejects = 0;
let intRejectsExactAccepts = 0;
const intAcceptDiffs = [];
const intRejectDiffs = [];
const bothSafe = (d, m) => Number.isSafeInteger(d) && Number.isSafeInteger(m) && m !== 0;
const intExpected = (d, m) => (bothSafe(d, m) ? BigInt(d) % BigInt(m) === 0n : multipleOfOk(d, m));
const intRecord = (engine, d, m, got) => {
  const want = intExpected(d, m);
  if (got === want) return;
  if (got) intAcceptsExactRejects++; else intRejectsExactAccepts++;
  const diffs = got ? intAcceptDiffs : intRejectDiffs;
  if (diffs.length < 8) diffs.push(`${engine}: ${d} % ${m}`);
};
// Every engine the block drives, built once for divisor m; the returned
// function runs d through all of them and through the library itself.
const intEngines = (m) => {
  const schema = { multipleOf: m };
  const t0 = new Validator(schema, { engine: 'interpreter' });
  const ipNot = new Validator(NOT_TIER0(schema), { engine: 'interpreter' });
  const cg = new Validator(schema);
  const closure = compileToJS(schema);
  const verdict = compileVerdict(schema, {});
  assert.ok(verdict !== null, `plan-source compiles ${JSON.stringify(schema)}`);
  const verdictNot = compileVerdict(NOT_TIER0(schema), {});
  const withErrors = compileToJSCodegenWithErrors(schema);
  const combined = compileToJSCombined(schema, COMBINED_VALID);
  const mod = { exports: {} };
  new Function('module', 'exports', toStandaloneModule(schema, { format: 'cjs' }))(mod, mod.exports);
  const once = (d) => {
    intRecord('multipleOfOk', d, m, multipleOfOk(d, m));
    if (Number.isSafeInteger(m) && m !== 0) intRecord('multipleOfInteger', d, m, multipleOfInteger(d, m));
    intRecord('tier 0 first call', d, m, new Validator(schema).isValidObject(d));
    intRecord('tier 0 every call', d, m, t0.isValidObject(d));
    intRecord('interpreter validate', d, m, t0.validate(d).valid);
    intRecord('interpreter walk', d, m, ipNot.validate(d).valid);
    intRecord('codegen validate', d, m, cg.validate(d).valid);
    intRecord('closure compiler', d, m, closure(d));
    intRecord('plan-source', d, m, verdict.fn(d));
    if (verdictNot !== null) intRecord('plan-source not', d, m, verdictNot.fn(d));
    intRecord('codegen with errors', d, m, withErrors(d).valid);
    intRecord('combined', d, m, combined(d).valid);
    intRecord('standalone', d, m, mod.exports.isValid(d));
  };
  const warm = (d) => {
    intRecord('generated isValidObject', d, m, cg.isValidObject(d));
    intRecord('interpreter closure tree', d, m, ipNot.isValidObject(d));
  };
  return (values) => {
    for (const d of values) once(d);
    for (let r = 0; r < 3; r++) for (const d of values) warm(d);
  };
};
for (const m of INT_DIVISORS) intEngines(m)(intValues(m).filter((d) => Number.isFinite(d)));

// Fixed safe-integer pairs, each expected answer written by hand and checked
// against BigInt here, through every engine.
const INT_FIXED = [
  [2 ** 53 - 1, 3, false],
  [2 ** 53 - 2, 2, true],
  [2 ** 32 * 3 + 1, 3, false],
  [2 ** 32 * 3, 3, true],
  [1700000000000, 1000, true],
  [1700000000001, 1000, false],
  [2 ** 53 - 1, 2 ** 53 - 1, true],
];
for (const [d0, m0, expected] of INT_FIXED) {
  for (const [d, m] of [[d0, m0], [-d0, m0], [d0, -m0], [-d0, -m0]]) {
    check(BigInt(d) % BigInt(m) === 0n, expected, `BigInt agrees with the written answer for ${d} % ${m}`);
    check(multipleOfOk(d, m), expected, `multipleOfOk(${d}, ${m})`);
    intEngines(m)([d]);
  }
}

// Seeded random safe-integer pairs in the range this path is for: |d| from
// 2^32 to 2^53 - 1, divisors of every size from 2 to 2^53 - 1, as exact
// multiples q * m (only where the product is a safe integer) and as
// q * m + e for e in -2, -1, 1, 2. Every pair goes through multipleOfOk and
// multipleOfInteger; every 40th divisor's pairs also go through the engines.
const randomSafe = (lo, hi) => {
  const span = hi - lo;
  const r = (dnext() * 2 ** 21 + (dnext() >>> 11)) / 2 ** 53;
  return Math.min(hi, lo + Math.floor(r * span));
};
let intRandomPairs = 0;
for (let i = 0; i < 1600; i++) {
  const m = randomSafe(2, 2 ** (2 + (dnext() % 52)) - 1) * (dnext() % 5 === 0 ? -1 : 1);
  const a = Math.abs(m);
  const qMax = Math.floor((2 ** 53 - 1 - 2) / a);
  const qMin = Math.ceil((2 ** 32 + 2) / a);
  const pairs = [];
  if (qMax >= 1) {
    const q = randomSafe(Math.min(qMin, qMax), qMax) * (dnext() % 2 ? 1 : -1);
    const base = q * m;
    for (const e of [0, -2, -1, 1, 2]) if (Number.isSafeInteger(base + e)) pairs.push(base + e);
  }
  for (const d of pairs) {
    intRandomPairs++;
    intRecord('multipleOfOk', d, m, multipleOfOk(d, m));
    intRecord('multipleOfInteger', d, m, multipleOfInteger(d, m));
  }
  if (i % 40 === 0 && pairs.length > 0) intEngines(m)(pairs);
}
check(intRandomPairs > 7000, true, `random safe-integer pairs ran (${intRandomPairs})`);

// The hoisted helper _mok that generated code carries is a copy of
// multipleOfOk written as text. The engines above do not reach its
// safe-integer branch, because generated code tests a safe integer against an
// integer divisor inline before any call, so the helper text is taken out of
// a standalone module here and run directly on seeded random safe-integer
// pairs of the same kind as above.
const helperText = (src, name) => {
  const start = src.indexOf(`function ${name}(`);
  assert.ok(start >= 0, `standalone module carries ${name}`);
  let depth = 0;
  for (let i = src.indexOf('{', start); i < src.length; i++) {
    if (src[i] === '{') depth++;
    else if (src[i] === '}' && --depth === 0) return src.slice(start, i + 1);
  }
  throw new Error(`unbalanced ${name}`);
};
const helperSrc = toStandaloneModule({ multipleOf: 0.01 }, { format: 'cjs' });
const _mokText = new Function(`${helperText(helperSrc, '_mok')}\nreturn _mok`)();
let helperPairs = 0;
dseed = 0x51ed;
for (let i = 0; i < 1000; i++) {
  const m = randomSafe(2, 2 ** (2 + (dnext() % 52)) - 1);
  const qMax = Math.floor((2 ** 53 - 3) / m);
  const q = randomSafe(Math.min(Math.ceil((2 ** 32 + 2) / m), qMax), qMax);
  for (const e of [0, -2, -1, 1, 2]) {
    const d = q * m + e;
    if (!Number.isSafeInteger(d)) continue;
    helperPairs++;
    intRecord('_mok helper text', d, m, _mokText(d, m));
  }
}
check(helperPairs > 4000, true, `_mok helper text ran on random pairs (${helperPairs})`);
check(intAcceptsExactRejects, 0, `integer divisor: an engine ACCEPTS values the exact rule rejects (silent acceptance): ${intAcceptDiffs.join('; ')}`);
check(intRejectsExactAccepts, 0, `integer divisor: an engine rejects values the exact rule accepts: ${intRejectDiffs.join('; ')}`);

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

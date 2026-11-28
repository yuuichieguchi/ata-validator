'use strict';

// Exact decimal multipleOf check shared by every JS engine.
//
// JSON Schema Validation 2020-12 section 6.2.1 says a number is valid when
// division by the keyword's value results in an integer. Dividing as IEEE-754
// doubles with a 1e-9 tolerance accepts non-multiples above 2^53 (1e20 / 3)
// and rejects multiples whose quotient overflows to Infinity (1e308 / 0.5).
//
// Two safe integers divide exactly in double arithmetic, so that case skips
// BigInt. Otherwise each number is read as its shortest round-trip decimal
// (String(Math.abs(v))) and tested for exact divisibility over a common power
// of ten using BigInt.

function parseDecimal(v) {
  let s = String(Math.abs(v));
  let exp = 0;
  const eIdx = s.indexOf('e');
  if (eIdx >= 0) {
    exp = Number(s.slice(eIdx + 1));
    s = s.slice(0, eIdx);
  }
  const dot = s.indexOf('.');
  if (dot >= 0) {
    exp -= s.length - dot - 1;
    s = s.slice(0, dot) + s.slice(dot + 1);
  }
  return { digits: BigInt(s), exp };
}

// Whether the safe integer m (not zero) divides the safe integer d, without
// the remainder operator. On Node 24, d % m measured 25 to 27 ns a call in two
// situations, a divisor read from an object field that had once held 0.01 and
// a value above 2^32, against about 1.4 ns for a value below 2^31 and a
// divisor that had only ever been a small integer. The quotient test measured
// 1.3 ns in both situations.
// The quotient test is exact for safe integers. When m divides d the quotient
// is an integer below 2^53 and the division gives it exactly (0 gives 0 or
// -0, both integers). When it does not, the true quotient is at least 1/|m|
// away from every integer and at least 1/|m| >= 2^-53 in magnitude, so it is
// not subnormal and the division's rounding error is at most |d / m| * 2^-53,
// which is below 1/|m| because |d| < 2^53: the double quotient is not an
// integer either.
function safeIntegerMultiple(d, m) {
  return Number.isInteger(d / m);
}

// Two safe integers are asked first: a safe integer is finite, so the
// finiteness tests below are not needed for them, and the integer case is the
// common one.
function multipleOfOk(data, divisor) {
  if (Number.isSafeInteger(data) && Number.isSafeInteger(divisor)) return divisor !== 0 && safeIntegerMultiple(data, divisor);
  if (!Number.isFinite(data) || !Number.isFinite(divisor) || divisor === 0) return false;
  const a = parseDecimal(data);
  const b = parseDecimal(divisor);
  const scale = a.exp < b.exp ? a.exp : b.exp;
  const dividend = a.digits * 10n ** BigInt(a.exp - scale);
  const step = b.digits * 10n ** BigInt(b.exp - scale);
  return dividend % step === 0n;
}

// The fast path for a decimal divisor such as 0.01. When a schema is
// compiled, decimalDivisor splits the divisor once into m = M / 10^k with
// 0 <= k <= 15 and M an integer no larger than 1e15, read from the same
// shortest decimal parseDecimal gives, so divisors String() prints in exponent
// form (1e-7 to 1e-15) are covered. P is 10^k built from its decimal text,
// which is exact; 10 ** k is not guaranteed to be. It returns null, meaning no
// fast path, for a divisor that is not finite, is zero, has more than 15
// fractional digits, has a positive decimal exponent (1e21), or whose M is
// above 1e15. An integer divisor (exponent 0, so k = 0) has no fast path
// either: two safe integers need no scaling (see safeIntegerMultiple and
// multipleOfInteger below), and the scaled test with P = 1 measured slower
// in generated code than a direct integer test.
function decimalDivisor(divisor) {
  if (!Number.isFinite(divisor) || divisor === 0) return null;
  const { digits, exp } = parseDecimal(divisor);
  if (exp >= 0 || exp < -15 || digits > 1000000000000000n) return null;
  return { P: Number('1e' + -exp), M: Number(digits) };
}

// The run-time check with the pair from decimalDivisor. n is the value scaled
// by 10^k and rounded. The bound is |n| <= 1e15 and not "n is a safe integer",
// because two facts hold only up to 1e15:
// (a) for |n| <= 1e15 the rounding error of d * P is below 0.5 (about 0.22 at
//     1e15), so Math.round returns the true scaled integer whenever the
//     value's decimal has at most k fractional digits;
// (b) two decimals of at most 15 significant digits never share a double, so
//     n / P === d means the shortest decimal of d is exactly n / 10^k.
// Both fail between 1e15 and 2^53: Math.round(38976600501045.13 * 100) / 100
// === 38976600501045.13 is false, though 38976600501045.13 is a multiple of
// 0.01. Everything outside the bound (exponents, huge values, NaN, Infinity)
// goes to multipleOfOk.
function multipleOfFast(data, divisor, P, M) {
  const n = Math.round(data * P);
  if (n <= 1e15 && n >= -1e15) return n / P === data && safeIntegerMultiple(n, M);
  return multipleOfOk(data, divisor);
}

// The compile-time test for an integer divisor: a safe integer other than 0.
// Such a divisor has no decimalDivisor pair; its schemas call
// multipleOfInteger, which answers a safe integer value without entering
// multipleOfOk and its BigInt reading.
function integerDivisor(divisor) {
  return Number.isSafeInteger(divisor) && divisor !== 0;
}

// The run-time check for a divisor integerDivisor accepted: a safe integer
// value is answered here, anything else (a fraction, a value above 2^53, NaN,
// Infinity) by multipleOfOk.
function multipleOfInteger(data, divisor) {
  return Number.isSafeInteger(data) ? safeIntegerMultiple(data, divisor) : multipleOfOk(data, divisor);
}

module.exports = { multipleOfOk, decimalDivisor, multipleOfFast, integerDivisor, multipleOfInteger };

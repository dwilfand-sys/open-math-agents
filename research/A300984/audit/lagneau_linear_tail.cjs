// node workSearch/lagneau_linear_tail.cjs 20000000 73 20000000 [upper] [s1,s2,...]
// Tests r and 2*s*r-1 for prime r=5 mod 6. Each slope is used only when s
// is the least prime divisor of M=(p+1)/2 that is 5 mod 6.
'use strict';

const base = require('./lagneau_crt_bound.cjs');
const bands = require('./lagneau_band_witnesses.cjs');
const graph = require('./lagneau_two_outer.cjs');

function primesAboveThree(limit) {
  const mark = new Uint8Array(limit+1), primes = [];
  for (let p = 5; p <= limit; p += 2) {
    if (p % 3 === 0 || mark[p]) continue;
    primes.push(p);
    for (let j = p*p; j <= limit; j += 2*p) mark[j] = 1;
  }
  return primes;
}

function inverse(a, q) {
  let x = 1, y = 0, u = a, v = q;
  while (v) {
    const t = Math.floor(u/v);
    [u, v] = [v, u-t*v];
    [x, y] = [y, x-t*y];
  }
  return u === 1 ? (x % q + q) % q : 0;
}

function pairMultiplier(lower, upper, slope, blockSize = 262144) {
  if (![lower, upper, slope, blockSize].every(Number.isSafeInteger) ||
      lower < 5 || lower >= upper || slope < 5 || slope % 6 !== 5 || blockSize < 1 ||
      2*slope*upper > Number.MAX_SAFE_INTEGER || upper > 1000000000000 ||
      (10*slope-1)*Math.ceil(Math.sqrt(2*slope*upper)) > Number.MAX_SAFE_INTEGER) {
    throw new RangeError('Invalid pair-sieve limits or slope');
  }
  const d = 5;
  const first = Math.floor((lower-d)/6)+1, last = Math.floor((upper-d)/6);
  const primes = primesAboveThree(Math.ceil(Math.sqrt(2*slope*upper)));
  const factors = [], starts = [];
  // A composite value of either linear form has a prime divisor at most its
  // square root. Starting at q² preserves the exceptional prime value q.
  for (const [a, b] of [[6, d], [12*slope, 2*slope*d-1]]) {
    for (const q of primes) {
      if (q*q > a*last+b) break;
      const inv = inverse(a, q);
      if (!inv) continue;
      const residue = ((-b*inv) % q + q) % q;
      const begin = Math.max(first, Math.ceil((q*q-b)/a));
      factors.push(q);
      starts.push(begin+(residue-begin%q+q)%q);
    }
  }
  const qs = Uint32Array.from(factors), next = Float64Array.from(starts);
  const mark = new Uint8Array(blockSize);
  let factor = base.scale, count = 0, blocks = 0;
  for (let start = first; start <= last; start += blockSize) {
    const length = Math.min(blockSize, last-start+1);
    mark.fill(0, 0, length);
    for (let j = 0; j < qs.length; j++) {
      let k = next[j]-start;
      for (; k < length; k += qs[j]) mark[k] = 1;
      next[j] = start+k;
    }
    let blockCount = 0;
    for (let i = 0; i < length; i++) blockCount += 1-mark[i];
    const maxPrime = BigInt(6*(start+length-1)+d);
    // The chance of r|M is at least 1/r even after conditioning on squarefree
    // F₂. A block with c exclusions therefore has survival at most M/(M+c).
    factor = base.ceilDiv(factor*maxPrime, maxPrime+BigInt(blockCount));
    count += blockCount;
    blocks++;
  }
  return {slope, lower, upper, count, blocks, factor};
}

function negativeTailGraph(factors, source = graph) {
  return {
    makeGraph(factor, family, cutoff) {
      return {data: source.makeGraph(factor, family, cutoff), small: family.small};
    },
    makeCorrection(g, weights) {
      const inner = source.makeCorrection(g.data, weights);
      const negativePrimes = g.small.map((r, i) => [r, 1 << i]).filter(([r]) => r % 6 === 5);
      return (weight, mask, seen) => {
        const initial = inner(weight, mask, seen);
        // The least negative residue prime is found among *all* small primes,
        // even if the requested list of slopes skips an intermediate prime.
        for (const [r, bit] of negativePrimes) {
          if (!(mask & bit)) continue;
          return factors.has(r) ? base.ceilDiv(initial*factors.get(r), base.scale) : initial;
        }
        return initial;
      };
    }
  };
}

function combine(factors, outerLimit, source = graph) {
  return bands.compute(negativeTailGraph(factors, source), outerLimit);
}

module.exports = {pairMultiplier, negativeTailGraph, combine};
if (require.main === module) {
  const outer = Number(process.argv[4] || base.maxDivisor);
  const upper = Number(process.argv[5] || 1000000000);
  const slopes = (process.argv[6] || '5,11,17').split(',').map(Number);
  const allowed = new Set(primesAboveThree(base.smallLimit).filter(r => r % 6 === 5));
  if (slopes.some(s => !allowed.has(s))) throw new Error('Choose small prime slopes that are 5 mod 6');
  if (slopes.some(s => Math.floor(base.maxDivisor/s) < base.smallLimit)) {
    throw new Error('The new prime interval must start at or beyond every small prime');
  }
  const readJSON = path => JSON.parse(require('node:fs').readFileSync(path, 'utf8'));
  const positivePath = process.argv[7], negativePath = process.argv[8];
  const saved = negativePath && negativePath !== '-' ? readJSON(negativePath) : null;
  if (saved && (saved.maxDivisor !== base.maxDivisor || saved.smallLimit !== base.smallLimit ||
      saved.upper !== upper || saved.blockSize !== 262144)) throw new Error('Wrong negative-slope table');
  const factors = new Map();
  for (const s of new Set(slopes)) {
    const lower = Math.floor(base.maxDivisor/s);
    const entry = saved && saved.slopes.find(row => row.s === s);
    if (saved && (!entry || entry.lower !== lower)) throw new Error('Missing negative slope');
    const r = saved ? {slope:s, lower, upper, count:entry.count, blocks:entry.blocks,
      factor:BigInt(entry.factor)} : pairMultiplier(lower, upper, s);
    if (r.factor < 0n || r.factor > base.scale) throw new Error('Invalid conditional multiplier');
    console.log({...r, factor: base.decimal(r.factor)});
    factors.set(s, r.factor);
  }
  let source = graph;
  if (positivePath && positivePath !== '-') {
    const pos = require('./lagneau_extra_residue_one.cjs'), table = readJSON(positivePath);
    if (table.maxDivisor !== base.maxDivisor || table.smallLimit !== base.smallLimit ||
        table.upper !== upper) throw new Error('Wrong positive-slope table');
    source = pos.positiveTailGraph(table);
  }
  const result = combine(factors, outer, source);
  console.log(result);
  if (base.maxDivisor === 20000000 && upper === 1000000000) {
    // Complementary post-D singleton certificates. Their primes are excluded
    // from all the positive-slope tests and have the opposite negative-slope residue.
    const stretch = process.argv[9] || '1B';
    if (!['1B','10B'].includes(stretch)) throw new Error('Choose singleton cutoff 1B or 10B');
    const singleton = stretch === '1B' ? 985858509556699n : 979789013592184n;
    const numerator = BigInt(result.numeratorUpper.replace('.', ''));
    const final = base.ceilDiv(numerator*singleton, base.scale);
    const denominator = 954160870567672n;
    console.log({singletonCutoff: stretch, combinedNumerator: base.decimal(final),
      combinedRatio: base.decimal(base.ceilDiv(final*base.scale, denominator))});
  }
}

// node workSearch/lagneau_band_witnesses.cjs [maximum divisor] [small prime cutoff]
// Append an outer-prime cutoff and --graph to use lagneau_two_outer.cjs as well.
'use strict';

const base = require('./lagneau_crt_bound.cjs');
const {maxDivisor, smallLimit, scale, ceilDiv, decimal} = base;
const lastExponent = 5;
const subsetCount = 1 << (lastExponent-1);

// For a fixed small prime r, classify each eligible residue class modulo r² by
// (i) r | (p+1)/2 and (ii) which F_i(p) vanish modulo r², for i = 2,...,5.
function localSquareTests(r) {
  const counts = Array.from({length: 2}, () => Array(subsetCount).fill(0));
  const modulus = r*r;
  for (let x = 1; x < modulus-1; x++) {
    if (x % r === 0) continue;
    let failures = 0;
    for (let i = 2; i <= lastExponent; i++) {
      const A = 2**(i+1)-1;
      const value = A*x*x + (A-3)*(x+1);
      if (!Number.isSafeInteger(value)) throw new Error('Polynomial value overflow');
      if (value % modulus === 0) failures |= 1 << (i-2);
    }
    counts[(x+1) % r === 0 ? 1 : 0][failures]++;
  }
  return counts.map(row => ({
    total: BigInt(row.reduce((a, b) => a+b, 0)),
    joint: row.map((_, subset) => BigInt(row.reduce((n, count, failures) =>
      n + ((failures & subset) ? 0 : count), 0)))
  }));
}

function makeWitnessUpper(family, factor) {
  const bits = new Map(family.small.map((r, i) => [r, 1 << i]));
  const tests = [];
  for (let r = 5; r <= smallLimit; r++) {
    if (factor[r] === r) tests.push({bit: bits.get(r) || 0, choices: localSquareTests(r)});
  }
  const subsets = [];
  for (let subset = 1; subset < subsetCount; subset++) {
    let size = 0;
    for (let remaining = subset; remaining; remaining &= remaining-1) size++;
    subsets.push({subset, positive: size % 2 === 1});
  }

  return function(mask) {
    const union = Array(lastExponent+1).fill(0n);
    for (const {subset, positive} of subsets) {
      let product = scale;
      for (const {bit, choices} of tests) {
        const {joint, total} = choices[(mask & bit) ? 1 : 0];
        const numerator = product * joint[subset];
        // Odd intersections enter inclusion-exclusion positively. Every partial
        // product is rounded up in that case, and down when it is subtracted.
        product = positive ? ceilDiv(numerator, total) : numerator/total;
      }
      for (let i = 2; i <= lastExponent; i++) {
        if (subset < 1 << (i-1)) union[i] += positive ? product : -product;
      }
    }
    for (let i = 2; i <= lastExponent; i++) {
      if (union[i] < 0n) throw new Error('Negative conditional probability');
      if (union[i] > scale) union[i] = scale;
    }
    return union;
  };
}

function compute(graphModule, outerLimit = maxDivisor) {
  const factor = base.smallestPrimeFactors(Math.max(2*maxDivisor, 100000));
  const family = base.obstructionFamily(factor);
  const conditional = makeWitnessUpper(family, factor);
  const sums = Array(lastExponent+1).fill(0n);
  if (!Number.isSafeInteger(outerLimit) || outerLimit < smallLimit || outerLimit > maxDivisor) {
    throw new RangeError('Invalid outer prime cutoff');
  }
  const edges = graphModule && graphModule.makeGraph(factor, family, outerLimit);
  function correction(firstWitness) {
    if (!graphModule) return weight => weight;
    return graphModule.makeCorrection(edges, r => [r-1,
      r*(r-1)-1-(firstWitness ? base.rootCount(r) : 0)]);
  }
  const graph = correction(false);

  const H = base.survivorUpper(family, false, (weight, mask, seen) => {
    const bound = graph(weight, mask, seen);
    const local = conditional(mask);
    for (let i = 3; i <= lastExponent; i++) sums[i] += ceilDiv(bound*local[i], scale);
    return bound;
  });
  // The callback weights exclude the common singleton factor. Restore it with
  // the same upper rounding as the base sieve.
  let singleton = scale;
  for (const r of family.singletons) {
    const total = BigInt(r*(r-1)-1);
    singleton = ceilDiv(singleton*(total-BigInt(r-1)), total);
  }
  const upper = sums.map(s => ceilDiv(singleton*s, scale));
  const U = base.survivorUpper(family, true, correction(true));
  upper[2] = ceilDiv(U * base.squarefreeInterval(factor).upper, scale);

  const l = 707106781186547n, u = l+1n;
  if (2n*l*l > scale*scale || 2n*u*u < scale*scale) throw new Error('Invalid sqrt interval');
  // Successive normalized band widths are 1-1/√2, 1/√2-1/2,
  // (1-1/√2)/2 and (1/√2-1/2)/2. The untested inner tail has width 1/4.
  const widths = [0n, 0n, scale-l, u-scale/2n, ceilDiv(scale-l, 2n),
    ceilDiv(u-scale/2n, 2n)];
  let numerator = H*(scale/4n);
  for (let i = 2; i <= lastExponent; i++) numerator += widths[i]*upper[i];
  numerator = ceilDiv(numerator, scale);
  // From the independent three-witness representation density certificate.
  const representedLower = scale-45839129432327n;
  return {maxDivisor, smallLimit, graph: Boolean(graphModule),
    ...(graphModule ? {outerLimit} : {}),
    bandUpper: upper.slice(2).map(decimal), innerUpper: decimal(H),
    numeratorUpper: decimal(numerator), representedLower: decimal(representedLower),
    ratioUpper: decimal(ceilDiv(numerator*scale, representedLower))};
}

module.exports = {makeWitnessUpper, compute};
if (require.main === module) {
  const optionalGraph = process.argv.includes('--graph') ? require('./lagneau_two_outer.cjs') : null;
  const outer = process.argv[4] && process.argv[4] !== '--graph' ? Number(process.argv[4]) : maxDivisor;
  console.log(compute(optionalGraph, outer));
}

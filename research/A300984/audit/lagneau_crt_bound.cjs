// Run with node workSearch/lagneau_crt_bound.cjs [maximum divisor] [small prime cutoff].
// Conditional densities are relative to primes p = 1 mod 12 with squarefree p+1.
// The admissible divisors of M=(p+1)/2 have d=1 mod 6 and 2d-1 prime.
// Finitely many exceptions with d=M have no effect on any density here.
'use strict';

const maxDivisor = Number(process.argv[2] || 10000000);
const smallLimit = Number(process.argv[3] || 61);
const squarefreeLimit = 100000;
const scale = 10n ** 15n;
if (!Number.isSafeInteger(maxDivisor) || maxDivisor < 7 || maxDivisor > 20000000 ||
    !Number.isSafeInteger(smallLimit) || smallLimit < 5 || smallLimit > maxDivisor) {
  throw new RangeError('Choose 7 <= maximum divisor <= 20000000 and 5 <= small prime cutoff <= maximum divisor.');
}

function smallestPrimeFactors(limit) {
  const factor = new Uint32Array(limit + 1);
  for (let p = 2; p <= limit; p++) {
    if (factor[p]) continue;
    factor[p] = p;
    for (let n = p*p; n <= limit; n += p) {
      if (!factor[n]) factor[n] = p;
    }
  }
  return factor;
}

function ceilDiv(x, y) { return (x + y - 1n) / y; }

// Number of reduced roots of F(x)=7x²+4x+4 modulo r², excluding x=-1 mod r².
// For r>=5, r!=7, its discriminant is -96 and its constant is nonzero mod r.
// At r=7 the sole root is x=34 mod 49, which also satisfies x=-1 mod 7.
function rootCount(r) {
  return r === 7 ? 1 : ([1, 5, 7, 11].includes(r % 24) ? 2 : 0);
}

function obstructionFamily(factor) {
  const single = new Uint8Array(maxDivisor + 1);
  const singletons = [];
  for (let r = 7; r <= maxDivisor; r += 6) {
    if (factor[r] === r && factor[2*r-1] === 2*r-1) {
      single[r] = 1;
      singletons.push(r);
    }
  }

  const small = [];
  const bit = new Map();
  for (let r = 5; r <= smallLimit; r++) {
    if (factor[r] !== r || single[r]) continue;
    if (small.length >= 22) throw new RangeError('This cutoff has more than 22 free small primes.');
    bit.set(r, 1 << small.length);
    small.push(r);
  }

  const forbidden = new Set();
  const outerByMask = new Map();
  for (let d = 7; d <= maxDivisor; d += 6) {
    if (factor[2*d-1] !== 2*d-1) continue;
    let n = d, mask = 0, outer = 0;
    while (n > 1) {
      const r = factor[n];
      n /= r;
      if (single[r] || n % r === 0 || (r > smallLimit && outer)) break;
      if (r <= smallLimit) mask |= bit.get(r);
      else outer = r;
      if (n > 1) continue;
      if (outer === 0) forbidden.add(mask);
      else {
        if (!outerByMask.has(mask)) outerByMask.set(mask, []);
        outerByMask.get(mask).push(outer);
      }
    }
  }
  return {singletons, small, forbidden: [...forbidden], outerByMask};
}

// Conditional on squarefreeness of p+1, the indicator r|M has local weights
// (r-1)/(r²-r-1), independent for distinct r by CRT and the PNT in progressions.
// Conditioning also on squarefreeness of F(p) just removes its local roots.
function survivorUpper(family, requireSquarefreeF, refineMask) {
  const {singletons, small, forbidden, outerByMask} = family;
  function multiplyWeight(upper, r, divides) {
    const total = BigInt(r*(r-1) - 1 - (requireSquarefreeF ? rootCount(r) : 0));
    const hits = BigInt(r - 1 - (requireSquarefreeF && r === 7 ? 1 : 0));
    return ceilDiv(upper * (divides ? hits : total-hits), total);
  }
  let noSingleton = scale;
  for (const r of singletons) noSingleton = multiplyWeight(noSingleton, r, false);

  const seen = new Uint32Array(maxDivisor + 1);
  let survivor = 0n;
  for (let mask = 0; mask < 1 << small.length; mask++) {
    if (forbidden.some(edge => (edge & mask) === edge)) continue;
    let weight = scale;
    for (let j = 0; j < small.length; j++) {
      weight = multiplyWeight(weight, small[j], Boolean(mask & (1 << j)));
    }
    for (const [edge, outerPrimes] of outerByMask) {
      if ((mask & edge) !== edge) continue;
      for (const r of outerPrimes) {
        if (seen[r] === mask+1) continue;
        seen[r] = mask+1;
        weight = multiplyWeight(weight, r, false);
      }
    }
    survivor += refineMask ? refineMask(weight, mask, seen) : weight;
  }
  return ceilDiv(noSingleton * survivor, scale);
}

function squarefreeInterval(factor) {
  let lower = scale, upper = scale;
  for (let r = 5; r <= squarefreeLimit; r++) {
    if (factor[r] !== r) continue;
    const t = BigInt(r*(r-1) - 1);
    const good = t - BigInt(rootCount(r));
    lower = lower*good/t;
    upper = ceilDiv(upper*good, t);
  }
  // Sum 2/((r-2)(r-1)) over every integer r>R to dominate the omitted mass.
  const R = BigInt(squarefreeLimit);
  lower = lower*(R-3n)/(R-1n);
  return {lower, upper};
}

function decimal(scaled) {
  return `${scaled/scale}.${String(scaled%scale).padStart(15, '0')}`;
}

function main() {
  const factor = smallestPrimeFactors(Math.max(2*maxDivisor, squarefreeLimit));
  const family = obstructionFamily(factor);
  const H = survivorUpper(family, false);
  const U = survivorUpper(family, true);
  const W = squarefreeInterval(factor);
  const witnessedBadLower = W.lower*(scale-U)/scale;
  // In the outside band P/sqrt(2)<p<=P (P=sqrt(X)/2), only n=4p² fits.
  // The coefficient of 1/sqrt(2) may have either sign when varying the cutoffs.
  const first = ceilDiv(U*W.upper, scale);
  const inverseSqrtLower = 707106781186547n;
  const inverseSqrtUpper = inverseSqrtLower+1n;
  if (2n*inverseSqrtLower**2n > scale**2n || 2n*inverseSqrtUpper**2n < scale**2n) {
    throw new Error('Invalid square-root interval');
  }
  const weight = H >= first ? inverseSqrtUpper : inverseSqrtLower;
  const numerator = ceilDiv(weight*H + (scale-weight)*first, scale);
  const ratio = ceilDiv(numerator*scale, numerator+witnessedBadLower);
  console.log({maxDivisor, smallLimit, singletons: family.singletons.length,
    smallPrimes: family.small, forbiddenSmallMasks: family.forbidden.length,
    oneOuterPrimeEdges: [...family.outerByMask.values()].reduce((n, a) => n+a.length, 0),
    eligiblePrimitiveUpper: decimal(H), eligibleSquarefreeFPrimitiveUpper: decimal(U),
    squarefreeFLower: decimal(W.lower), squarefreeFUpper: decimal(W.upper),
    representedNonprimitiveLower: decimal(witnessedBadLower), representedPrimitiveUpper: decimal(numerator),
    upperRepresentedRatio: decimal(ratio)});
}

module.exports = {maxDivisor, smallLimit, scale, ceilDiv, decimal, rootCount,
  smallestPrimeFactors, obstructionFamily, survivorUpper, squarefreeInterval};
if (require.main === module) main();

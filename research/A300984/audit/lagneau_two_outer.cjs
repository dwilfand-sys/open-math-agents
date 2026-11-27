// node lagneau_two_outer.cjs [maximum divisor] [small cutoff] [outer cutoff]
'use strict';
const base = require('./lagneau_crt_bound.cjs');
const {maxDivisor, smallLimit, scale, ceilDiv, decimal} = base;
function makeGraph(factor, family, outerLimit=maxDivisor) {
  if (!Number.isSafeInteger(outerLimit) || outerLimit < smallLimit ||
      outerLimit > maxDivisor) throw new RangeError('Invalid outer cutoff.');
  const single = new Set(family.singletons);
  const bits = new Map(family.small.map((r,i) => [r,1 << i]));
  const occurrences = new Map();
  const vertices = new Map();
  function vertex(r) {
    if (!vertices.has(r)) vertices.set(r,vertices.size);
    return vertices.get(r);
  }
  for (let d = 7; d <= maxDivisor; d += 6) {
    if (factor[2*d-1] !== 2*d-1) continue;
    let n = d, smallMask = 0, r = 0, s = 0;
    while (n > 1) {
      const q = factor[n];
      n /= q;
      if (n % q === 0 || single.has(q) || q > outerLimit) break;
      if (q <= smallLimit) smallMask |= bits.get(q);
      else if (!r) r = q;
      else if (!s) s = q;
      else break;
      if (n !== 1 || !s) continue;
      const key = r*(outerLimit+1) + s;
      if (!occurrences.has(key)) occurrences.set(key,{i:vertex(r),j:vertex(s),masks:[]});
      const edge = occurrences.get(key);
      if (edge.masks.some(m => (m & smallMask) === m)) continue;
      edge.masks = edge.masks.filter(m => (m & smallMask) !== smallMask);
      edge.masks.push(smallMask);
    }
  }
  return {primes:[...vertices.keys()], edges:[...occurrences.values()]};
}

const precision = 10000000;
const S = BigInt(precision), S2 = S*S, S4 = S2*S2;
function exact(value) {
  if (!Number.isSafeInteger(value) || value < 0) throw new Error('Integer overflow');
  return BigInt(value);
}

function makeCorrection(graph, hitsTotal) {
  const {primes,edges} = graph;
  const lo = [], hi = [];
  for (const r of primes) {
    const [hitCount,totalCount] = hitsTotal(r);
    const hits = BigInt(hitCount), total = BigInt(totalCount);
    if (hits < 0n || hits > total || total <= 0n) throw new Error('Invalid local probability');
    lo.push(Number(S*hits/total));
    hi.push(Number(ceilDiv(S*hits,total)));
  }
  const neighbourSums = new Float64Array(primes.length);
  const neighbourSquares = new Float64Array(primes.length);
  return function refine(weight, mask, seen) {
    // Masks of four or more selected small primes have very little mass.
    // Leaving their old certified bound intact saves work.
    let m = mask;
    for (let k=0; k<3; k++) m &= m-1;
    if (m) return weight;
    neighbourSums.fill(0);
    neighbourSquares.fill(0);
    let lowerSum = 0, upperSum = 0;
    for (const {i,j,masks} of edges) {
      if (seen[primes[i]]===mask+1 || seen[primes[j]]===mask+1) continue;
      if (!masks.some(t => (mask&t)===t)) continue;
      lowerSum += lo[i]*lo[j];
      upperSum += hi[i]*hi[j];
      neighbourSums[i] += hi[j];
      neighbourSums[j] += hi[i];
      neighbourSquares[i] += hi[j]*hi[j];
      neighbourSquares[j] += hi[i]*hi[i];
    }
    const first = exact(lowerSum), firstUpper = exact(upperSum);
    let stars = 0n;
    for (let i=0; i<primes.length; i++) {
      const a = exact(neighbourSums[i]);
      stars += BigInt(hi[i])*(a*a-exact(neighbourSquares[i]));
    }
    // Bonferroni of order two. Squaring the total edge weight bounds all
    // disjoint-edge ordered intersections from above. For ordered adjacent
    // edges sum p_i p_j p_k at the common vertex i. The two sums may
    // double-count a positive amount, which preserves the upper bound.
    const den = 2n*S4;
    const num = den - 2n*first*S2 + firstUpper*firstUpper + stars*S;
    if (num < 0n) throw new Error('Negative survival bound');
    return num >= den ? weight : ceilDiv(weight*num,den);
  };
}

function main() {
  const outerLimit = Number(process.argv[4] || maxDivisor);
  const factor = base.smallestPrimeFactors(Math.max(2*maxDivisor,100000));
  const family = base.obstructionFamily(factor);
  const graph = makeGraph(factor,family,outerLimit);
  // All outer vertices are greater than seven. For F=7p²+4p+4, a root in
  // the hits p=-1 mod r would require r|F(-1)=7.
  const refinement = squarefreeF => makeCorrection(graph, r =>
    [r-1,r*(r-1)-1-(squarefreeF ? base.rootCount(r) : 0)]);
  const H = base.survivorUpper(family,false,refinement(false));
  const U = base.survivorUpper(family,true,refinement(true));
  const W = base.squarefreeInterval(factor);
  const l = 707106781186547n, u = l+1n;
  if (2n*l*l >= scale*scale || 2n*u*u <= scale*scale) throw new Error('Invalid sqrt bounds');
  const top = ceilDiv(U*W.upper,scale);
  const weight = H >= top ? u : l;
  const numerator = ceilDiv(weight*H + (scale-weight)*top,scale);
  // Bound the same three-shell denominator as the density audit on the scale.
  const inner2 = 6980795097n*1000n+ceilDiv(2n*scale,19999n);
  const inner3 = 207592750n*1000n+ceilDiv(3n*scale,19999n);
  const lost = ceilDiv((scale-l)*(scale-W.lower)+(u-scale/2n)*inner2+(scale/2n)*inner3,scale);
  const represented = scale-lost;
  console.log({maxDivisor,smallLimit,outerLimit,graphVertices:graph.primes.length,
    distinctAdditionalEdges:graph.edges.length,
    eligiblePrimitiveUpper:decimal(H),eligibleSquarefreeFPrimitiveUpper:decimal(U),
    representedPrimitiveUpper:decimal(numerator),representedLower:decimal(represented),
    primitiveAmongRepresentedUpper:decimal(ceilDiv(numerator*scale,represented))});
}

module.exports = {makeGraph,makeCorrection};
if (require.main === module) main();

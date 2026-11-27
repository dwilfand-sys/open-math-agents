// Sieve r and 2r-1 simultaneously for lower < r <= upper and r = 1 mod 6.
// node lagneau_large_singletons.cjs [lower] [upper] [numerator bound, scaled by 10^15]
'use strict';
const scale = 10n**15n;
const ceil = (v,d) => (v+d-1n)/d;
const decimal = y => String(y/scale)+'.'+String(y%scale).padStart(15,'0');

function basePrimes(maximum) {
  const composite = new Uint8Array(maximum+1), primes = [];
  for (let i=2;i<=maximum;i++) {
    if (composite[i]) continue;
    primes.push(i);
    for (let j=i*i;j<=maximum;j+=i) composite[j]=1;
  }
  return primes;
}

// For k in this residue class, q divides m*k+1.
function root(q,m) {
  for (let t=1;t<m;t++) if ((q*t)%m===1) return (q*t-1)/m;
  throw new Error('The modulus must be coprime to the step');
}

function bound(lower,upper,blockSize=65536) {
  if (!Number.isSafeInteger(lower) || !Number.isSafeInteger(upper) ||
      !Number.isSafeInteger(blockSize) || blockSize<=0 || lower<5 ||
      lower>=upper || upper>10**13) throw new RangeError('Invalid sieve bounds');
  const maxFactor = Math.ceil(Math.sqrt(2*upper));
  if (maxFactor*maxFactor<2*upper) throw new Error('Insufficient trial factors');
  // The entire production interval is above the trial factors. For a small
  // regression fixture the sieve also preserves the exceptional values r=q
  // or 2r-1=q by starting at the corresponding square.
  const qs = basePrimes(maxFactor).filter(q=>q>=5);
  const progressions = qs.flatMap(q => [6,12].map(m => ({
    q, residue:root(q,m), first:Math.ceil((q*q-1)/m)
  })));
  const firstK = Math.floor((lower-1)/6)+1, lastK=Math.floor((upper-1)/6);
  const marked = new Uint8Array(blockSize);
  let factor=scale, total=0, blocks=0;
  for (let low=firstK;low<=lastK;low+=blockSize) {
    const end=Math.min(low+blockSize,lastK+1), length=end-low;
    marked.fill(0,0,length);
    for (const {q,residue,first} of progressions) {
      const begin=Math.max(low,first), shift=(residue-begin%q+q)%q;
      for (let k=begin+shift-low;k<length;k+=q) marked[k]=1;
    }
    let count=0;
    for (let j=0;j<length;j++) count+=1-marked[j];
    const maximum=BigInt(6*(end-1)+1);
    // Each located prime removes at least 1/maximum of its local mass.
    // (1-1/M)^c <= 1/(1+c/M) by the binomial inequality.
    factor=ceil(factor*maximum,maximum+BigInt(count));
    total+=count;
    blocks++;
  }
  return {total,blocks,factor};
}

function main() {
  const lower=Number(process.argv[2]||20000000), upper=Number(process.argv[3]||1000000000);
  const old=BigInt(process.argv[4]||'511956779267551');
  if (lower<20000000) throw new RangeError('Use the published graph cutoff or a larger lower endpoint');
  if (old<=0n || old>scale) throw new RangeError('Invalid input numerator');
  const {total,blocks,factor}=bound(lower,upper);
  const numerator=ceil(old*factor,scale);
  const denominator=954160870567672n;
  console.log({lower,upper,blocks,shiftedPrimePairs:total,multiplierUpper:decimal(factor),
    representedPrimitiveUpper:decimal(numerator),representedLower:decimal(denominator),
    primitiveAmongRepresentedUpper:decimal(ceil(numerator*scale,denominator))});
}
module.exports={bound};
if (require.main===module) main();

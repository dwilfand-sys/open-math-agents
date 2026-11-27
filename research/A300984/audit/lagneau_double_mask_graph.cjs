// Janson bounds conditional on exactly two selected small primes in (p+1)/2.
// Usage: node lagneau_double_mask_graph.cjs 1000000000 73 12 Double.json
'use strict';
const fs = require('node:fs');
const {makeInputs}=require('./lagneau_wide_graph.cjs');
const S=100000000, scale=10n**15n, bigS=BigInt(S);

function numberAsBigInt(n) {
  if (!Number.isSafeInteger(n) || n < 0) throw new Error('Unsafe integer sum');
  return BigInt(n);
}

function survival(first, stars) {
  const numerator=2n*first*bigS-stars, denominator=2n*bigS**3n;
  if (numerator <= 0n) return scale;
  let sum=1n, den=1n, power=1n;
  for (let j=1n; j<=6n; j++) {
    power*=numerator;
    sum=sum*denominator*j+power;
    den*=denominator*j;
  }
  return (scale*den+sum-1n)/sum;
}

function graphRow(inputs, cap, small, a, b) {
  const {isPrime,vertices}=inputs;
  const multiples=[1,a,b,a*b];
  const max=Math.floor(cap/Math.max(small+1, a*b));
  const v=Uint32Array.from(vertices.filter(r =>
    r<=max && multiples.every(d=>!isPrime(2*d*r-1))));
  const lo=Uint32Array.from(v,r=>Math.floor(S/r));
  const hi=Uint32Array.from(v,r=>Math.ceil(S/(r-1)));
  const sums=new Float64Array(v.length);
  const squares=new Float64Array(v.length);
  let edges=0, first=0;
  for (let i=0; i<v.length && v[i]*v[i]<cap; i++) {
    for (let j=i+1; j<v.length && v[i]*v[j]<=cap; j++) {
      const prod=v[i]*v[j];
      if (!multiples.some(d=>d*prod<=cap && isPrime(2*d*prod-1))) continue;
      edges++; first+=lo[i]*lo[j];
      sums[i]+=hi[j]; squares[i]+=hi[j]*hi[j];
      sums[j]+=hi[i]; squares[j]+=hi[i]*hi[i];
    }
  }
  let stars=0n;
  for (let i=0; i<v.length; i++) {
    const t=numberAsBigInt(sums[i]);
    stars+=BigInt(hi[i])*(t*t-numberAsBigInt(squares[i]));
  }
  const ub=survival(numberAsBigInt(first),stars);
  return {selected:[a,b],vertexMax:max,vertices:v.length,edges,
    lowerFirst:String(first),upperOrderedStars:String(stars),survivalUpper:String(ub)};
}

if (require.main===module) {
  const cap=Number(process.argv[2]), small=Number(process.argv[3]), count=Number(process.argv[4]);
  if (!Number.isInteger(count) || count<1) throw new Error('Choose a positive row limit');
  const inputs=makeInputs(cap,small);
  const primes=[];
  for (let p=5; p<=small; p++)
    if (inputs.isPrime(p) && !inputs.isPrime(2*p-1)) primes.push(p);
  const pairs=primes.flatMap((a,i)=>primes.slice(i+1)
    .filter(b=>!inputs.isPrime(2*a*b-1)).map(b=>[a,b]));
  pairs.sort(([a,b],[c,d])=>a*b-c*d);
  const rows=[];
  for (const [a,b] of pairs.slice(0,count)) {
    const row=graphRow(inputs,cap,small,a,b);
    rows.push(row); console.log(a,b,row.edges,row.survivalUpper);
  }
  fs.writeFileSync(process.argv[5],JSON.stringify({cap,B:small,precision:S,rows},null,2)+'\n');
}
module.exports={graphRow};

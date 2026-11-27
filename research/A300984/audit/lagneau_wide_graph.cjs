// Graph of obstruction divisors up to a larger cutoff, on one chosen small prime.
'use strict';
const scale=10n**15n, S=100000000, s=BigInt(S);
const ceil=(x,y)=>(x+y-1n)/y;

function packedPrimes(cap) {
  const bytes=new Uint8Array(Math.ceil((cap+1)/16));
  bytes[0]=1;
  function prime(n) {
    if(n===2)return true;
    if(n<3 || n%2===0 || n>cap)return false;
    const i=Math.floor(n/2);
    return !(bytes[i>>>3]&(1<<(i&7)));
  }
  for(let q=3;q*q<=cap;q+=2) {
    if(!prime(q)) continue;
    for(let i=(q*q-1)/2;i<(cap+1)/2;i+=q) bytes[i>>>3]|=1<<(i&7);
  }
  return prime;
}
function exact(n) {
  if(!Number.isSafeInteger(n) || n<0)throw new Error('Integer overflow');
  return BigInt(n);
}
function makeInputs(cap,B) {
  if(!Number.isSafeInteger(cap)||cap<10000||cap>2000000000||B<5)throw new Error('Invalid cutoff');
  const isPrime=packedPrimes(2*cap);
  const vertices=[];
  for(let r=B+1;r<=Math.floor(cap/(B+1));r++) {
    if(isPrime(r) && !isPrime(2*r-1))vertices.push(r);
  }
  return {vertices,isPrime};
}
function graphBound(inputs,cap,B,t) {
  const {vertices,isPrime}=inputs;
  if(t && (!isPrime(t)||t>B||isPrime(2*t-1)))throw new Error('Invalid free small prime');
  // With zero or one small prime selected, every possible one-large rule
  // at a remaining vertex has multiplier 1 or t. Omit the whole support
  // of those rules, including all later linear exclusions at that vertex.
  const v=Uint32Array.from(t?vertices.filter(r=>!isPrime(2*t*r-1)):vertices);
  const l=new Uint32Array(v.length),u=new Uint32Array(v.length);
  for(let i=0;i<v.length;i++) {
    l[i]=Math.floor(S/v[i]);u[i]=Math.ceil(S/(v[i]-1));
    if(l[i]*v[i]>S || u[i]*(v[i]-1)<S) throw new Error('Invalid local rounding');
  }
  const sum=new Float64Array(v.length),sq=new Float64Array(v.length);
  let first=0,edges=0;
  for(let i=0;i<v.length&&v[i]*v[i]<cap;i++) {
    const r=v[i], hi=Math.floor(cap/r);
    for(let j=i+1;j<v.length&&v[j]<=hi;j++) {
      const d=r*v[j];
      if(!isPrime(2*d-1) && !(t && t*d<=cap && isPrime(2*t*d-1)))continue;
      edges++;first+=l[i]*l[j];
      sum[i]+=u[j];sum[j]+=u[i];
      sq[i]+=u[j]*u[j];sq[j]+=u[i]*u[i];
    }
  }
  let stars=0n;
  for(let i=0;i<v.length;i++) {
    const z=exact(sum[i]);
    stars+=BigInt(u[i])*(z*z-exact(sq[i]));
  }
  // Janson: Pr(no edge) <= exp(-mu+Delta/2), where Delta orders the
  // distinct touching edges. A rational lower Taylor sum for exp gives
  // an outward integer bound on its reciprocal.
  const num=2n*exact(first)*s-stars, den=2n*s**3n;
  let upper=scale;
  if(num>0n) {
    let a=1n,b=1n, termA=1n,termB=1n;
    for(let n=1n;n<=6n;n++) {
      termA*=num;termB*=den*n;
      // Multiplying the previous sum by the next term's denominator ratio
      // keeps the intermediate integers on one common Taylor denominator.
      a=a*(den*n)+termA;b=termB;
    }
    upper=ceil(scale*b,a);
  }
  return {small:t,vertices:v.length,edges,lowerFirst:String(first),
    upperOrderedStars:String(stars),survivalUpper:String(upper)};
}
function augment(table,source=require('./lagneau_two_outer.cjs')) {
  const values=new Map(table.rows.map(r=>[r.small,BigInt(r.survivalUpper)]));
  return {
    makeGraph(factor,family,outer) {
      if(table.B!==require('./lagneau_crt_bound.cjs').smallLimit)throw new Error('Small cutoff mismatch');
      return {core:source.makeGraph(factor,family,outer),small:family.small};
    },
    makeCorrection(state,weights) {
      const original=source.makeCorrection(state.core,weights);
      return (weight,mask,seen)=>{
        const old=original(weight,mask,seen);
        if(mask && (mask&(mask-1)))return old;
        const t=mask?state.small[Math.log2(mask)]:0;
        if(!values.has(t))return old;
        const extra=ceil(weight*values.get(t),scale);
        return old<extra?old:extra;
      };
    }
  };
}
module.exports={packedPrimes,makeInputs,graphBound,augment};
if(require.main===module) {
  const cap=Number(process.argv[2]||1000000000),B=Number(process.argv[3]||73);
  const inputs=makeInputs(cap,B),small=[0];
  for(let q=5;q<=B;q++) if(inputs.isPrime(q)&&!inputs.isPrime(2*q-1))small.push(q);
  const rows=[];
  for(const t of small) {
    const row=graphBound(inputs,cap,B,t);rows.push(row);
    console.log(t,row.edges,row.survivalUpper);
  }
  if(process.argv[4])require('node:fs').writeFileSync(process.argv[4],
    JSON.stringify({cap,B,precision:S,rows},null,2)+'\n');
}

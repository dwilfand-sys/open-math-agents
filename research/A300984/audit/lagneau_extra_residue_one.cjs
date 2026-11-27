// Additional obstruction divisors s*r for primes r = 1 mod 6.
// node lagneau_extra_residue_one.cjs [maximum divisor] [small cutoff] [new prime limit]
'use strict';
const {maxDivisor,smallLimit,scale,ceilDiv,decimal} = require('./lagneau_crt_bound.cjs');
const slopes=[13,43,61,67,73];
const masks=1<<slopes.length;
const smallThresholds=[13,43,55,61,67,73];

function trialPrimes(end) {
  const composite=new Uint8Array(end+1), out=[];
  for (let q=2;q<=end;q++) {
    if(composite[q]) continue;
    out.push(q);
    for(let n=q*q;n<=end;n+=q) composite[n]=1;
  }
  return out;
}
function inverse(a,q) {
  let r=q,s=a%q,u=0,v=1;
  while(s) {
    const z=Math.floor(r/s);
    [r,s]=[s,r-z*s];[u,v]=[v,u-z*v];
  }
  if(r!==1) throw new Error('Nonunit slope.');
  return (u%q+q)%q;
}
function progression(m,c,qs,max) {
  const rows=[];
  for(const q of qs) {
    if(q*q>max) break;
    if(m%q===0) {
      if(c%q===0) throw new Error('Nonprimitive polynomial.');
      continue;
    }
    const residue=(q-(c%q)*inverse(m,q)%q)%q;
    rows.push([q,residue,Math.ceil((q*q-c)/m)]);
  }
  return rows;
}
function flagComposites(array,rows,low,length) {
  array.fill(0,0,length);
  for(const [q,residue,start] of rows) {
    const begin=Math.max(low,start);
    for(let n=begin+(residue-begin%q+q)%q-low;n<length;n+=q) array[n]=1;
  }
}
function build(D,B,upper,blockSize=65536,fixedLower=null) {
  if(B<73 || !Number.isSafeInteger(D) || !Number.isSafeInteger(upper) ||
     upper<=D || upper>10**10 || D<10000 || blockSize<1 || !Number.isSafeInteger(blockSize)) {
    throw new Error('Require B >= 73, D >= 10000, and D < upper <= 10^10.');
  }
  const max=2*upper*slopes.at(-1), lastQ=Math.ceil(Math.sqrt(max));
  if(lastQ*lastQ<max) throw new Error('Incomplete trial factors.');
  const qs=trialPrimes(lastQ);
  const primeP=progression(6,1,qs,upper);
  const primeSingleton=progression(12,1,qs,2*upper-1);
  const linear=slopes.map(t=>progression(12*t,2*t-1,qs,2*t*upper-1));
  const rComp=new Uint8Array(blockSize), singleComp=new Uint8Array(blockSize);
  const flags=slopes.map(()=>new Uint8Array(blockSize));
  const factors=smallThresholds.map(()=>Array(masks).fill(scale));
  const counts=smallThresholds.map(()=>Array(masks).fill(0));
  if(fixedLower!==null && (!Number.isSafeInteger(fixedLower) || fixedLower<D || fixedLower>=upper)) {
    throw new Error('The extension must start beyond the old divisor search.');
  }
  const boundaries=fixedLower===null
    ? [...new Set(smallThresholds.map(t=>Math.floor(D/t)).concat(upper))].sort((a,b)=>a-b)
    : [fixedLower, upper];
  for(let z=1;z<boundaries.length;z++) {
    const left=boundaries[z-1], right=boundaries[z];
    const start=Math.floor((left-1)/6)+1, stop=Math.floor((right-1)/6)+1;
    for(let low=start;low<stop;low+=blockSize) {
      const end=Math.min(stop,low+blockSize), len=end-low;
      flagComposites(rComp,primeP,low,len);
      flagComposites(singleComp,primeSingleton,low,len);
      for(let j=0;j<slopes.length;j++) flagComposites(flags[j],linear[j],low,len);
      const h=new Uint32Array(masks);
      for(let k=0;k<len;k++) {
        if(rComp[k] || !singleComp[k]) continue;
        let key=0;
        for(let j=0;j<slopes.length;j++) if(!flags[j][k]) key|=1<<j;
        h[key]++;
      }
      // After this transform h[A] counts signatures contained in A.
      for(let j=0;j<slopes.length;j++) for(let a=0;a<masks;a++) {
        if(a&(1<<j)) h[a]+=h[a^(1<<j)];
      }
      const M=BigInt(6*(end-1)+1);
      for(let n=0;n<smallThresholds.length;n++) {
        if(left<Math.floor(D/smallThresholds[n])) continue;
        for(let a=1;a<masks;a++) {
          const c=h[masks-1]-h[(masks-1)^a];
          factors[n][a]=ceilDiv(factors[n][a]*M,M+BigInt(c));
          counts[n][a]+=c;
        }
      }
    }
  }
  return {factors,counts};
}
function byMask(family,table) {
  const memo=new Map();
  function factorFor(mask) {
    const selected=family.small.filter((_,j)=>mask&(1<<j));
    let bits=0;
    for(let j=0;j<slopes.length;j++) if(selected.includes(slopes[j])) bits|=1<<j;
    if(!bits) return scale;
    const oddClass=selected.filter(r=>r%6===5).sort((a,b)=>a-b);
    const least=Math.min(...selected.filter(r=>r%6===1),
      oddClass.length>=2 ? oddClass[0]*oddClass[1] : Infinity);
    // For an extended small cutoff, round the threshold down to a supported
    // one: a larger lower endpoint for r remains a valid independent family.
    const index=smallThresholds.reduce((ans,t,i)=>t<=least ? i : ans,-1);
    if(index<0) return scale;
    return BigInt(table.factors[index][bits]);
  }
  return mask=>{
    if(!memo.has(mask)) memo.set(mask,factorFor(mask));
    return memo.get(mask);
  };
}
function positiveTailGraph(table,source=require('./lagneau_two_outer.cjs')) {
  return {
    makeGraph(factor,family,outer) {
      return {core:source.makeGraph(factor,family,outer),multiplier:byMask(family,table)};
    },
    makeCorrection(state,hitsTotal) {
      const original=source.makeCorrection(state.core,hitsTotal);
      return (weight,mask,seen)=>ceilDiv(original(weight,mask,seen)*state.multiplier(mask),scale);
    }
  };
}
module.exports={build,byMask,positiveTailGraph,slopes,smallThresholds};
if(require.main===module) {
  const upper=Number(process.argv[4]||1000000000);
  const table=build(maxDivisor,smallLimit,upper);
  if(process.argv[5]) {
    const output={maxDivisor,smallLimit,upper,blockSize:65536,slopes,smallThresholds,...table};
    require('node:fs').writeFileSync(process.argv[5],JSON.stringify(output,
      (_,v)=>typeof v==='bigint'?String(v):v,2)+'\n');
  }
  for(let i=0;i<slopes.length;i++) {
    const n=smallThresholds.indexOf(slopes[i]), a=1<<i;
    console.log(slopes[i],table.counts[n][a],decimal(table.factors[n][a]));
  }
}

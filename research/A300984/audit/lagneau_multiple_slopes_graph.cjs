'use strict';
const fs=require('node:fs');
const {ceilDiv,scale}=require('./lagneau_crt_bound.cjs');
const slopes=[5,11,17,23,29,41,47,53,59,71];
function read(name,lower,upper) {
  const data=fs.readFileSync(name);
  const plain=name.endsWith('.gz') ? require('node:zlib').gunzipSync(data) : data;
  const rows=plain.toString('utf8').trim().split('\n').map(x=>x.trim().split(/\s+/));
  if(rows.length!==1<<slopes.length)throw Error('Incomplete small-slope choices');
  return rows.map(([a,b,i,n,f],j)=>{
    if(Number(a)!==lower||Number(b)!==upper||Number(i)!==j||Number(n)<0||BigInt(f)<=0n||BigInt(f)>scale)
      throw Error('Bad small-slope row '+j);
    return BigInt(f);
  });
}
function extend(table,source) {
  return {
    makeGraph(factor,family,outer) {
      const bits=slopes.map(s=>family.small.indexOf(s));
      if(bits.some(i=>i<0))throw Error('Missing small prime');
      return {core:source.makeGraph(factor,family,outer),bits};
    },
    makeCorrection(state,weights) {
      const inner=source.makeCorrection(state.core,weights);
      return (weight,mask,seen)=>{
        const selected=state.bits.reduce((a,j,i)=>a+((mask&(1<<j))?1<<i:0),0);
        return ceilDiv(inner(weight,mask,seen)*table[selected],scale);
      };
    }
  };
}
module.exports={read,extend};

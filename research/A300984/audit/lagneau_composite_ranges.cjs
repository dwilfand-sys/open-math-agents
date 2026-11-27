'use strict';
const fs=require('node:fs'),path=require('node:path');
const {scale,ceilDiv}=require('./lagneau_crt_bound.cjs');
const divisors=require('./lagneau_composite_slopes.cjs');
const ranges={
  '50K400K':['separate',50_000,400_000],
  '4M14M':['short',4_000_000,14_000_000],
  '14M100M':['short',14_000_000,100_000_000],
  '100M1B':['long',100_000_000,1_000_000_000],
  '3B4B':['separate',3_000_000_000,4_000_000_000],
  '400K4M':['separate',400_000,4_000_000]
};
function multiply(f,g) {
  if(!f)return g;
  if(!g)return f;
  return (mask,small)=>ceilDiv(f(mask,small)*g(mask,small),scale);
}
function open(manifest) {
  const result={negative:{},positive:{},separate:[]};
  if(!manifest || manifest==='-')return result;
  const spec=JSON.parse(fs.readFileSync(manifest,'utf8')),directory=path.dirname(manifest);
  if(!Array.isArray(spec.ranges)||new Set(spec.ranges).size!==spec.ranges.length)throw Error('Bad composite manifest');
  const remaining=new Set(spec.remaining||[]);
  if([...remaining].some(key=>!spec.ranges.includes(key)||!['400K4M','4M14M','14M100M'].includes(key)))
    throw Error('Invalid remaining-pair range');
  for(const key of spec.ranges) {
    if(!Object.hasOwn(ranges,key))throw Error('Unknown composite range');
    const [stage,lo,hi]=ranges[key];
    for(const [sign,word] of [[5,'Negative'],[1,'Positive']]) {
      const name=path.join(directory,'CunninghamComposite'+word+key+'.txt');
      let table=divisors.read(fs.existsSync(name)?name:name+'.gz',sign,lo,hi);
      if(remaining.has(key)) {
        const more=path.join(directory,'CunninghamCompositeRemaining'+word+key+'.txt');
        table=divisors.merge(table,divisors.read(fs.existsSync(more)?more:more+'.gz',sign,lo,hi,true));
      }
      if(stage==='separate')result.separate.push(table);
      else {
        const group=result[word.toLowerCase()];
        group[stage]=multiply(group[stage],divisors.callback(table));
      }
    }
  }
  return result;
}
module.exports={open,multiply,extend:divisors.extend};

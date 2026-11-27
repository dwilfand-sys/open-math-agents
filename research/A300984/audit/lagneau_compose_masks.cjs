// Compose two-selected-prime graphs with the verified zero/one-prime tables.
// Usage: node lagneau_compose_masks.cjs 20000000 73 combined.json double.json positive.json negative.json
'use strict';
const fs=require('node:fs');
const base=require('./lagneau_crt_bound.cjs');
const {augment}=require('./lagneau_wide_graph.cjs');
const {positiveTailGraph}=require('./lagneau_extra_residue_one.cjs');
const {combine}=require('./lagneau_linear_tail.cjs');
const read=p=>JSON.parse(fs.readFileSync(p,'utf8'));

function augmentDouble(table, source) {
  return {
    makeGraph(factor,family,outer) {
      if(table.B!==base.smallLimit || table.cap!==1000000000)throw new Error('Unexpected graph dimensions');
      const values=new Map();
      for(const row of table.rows) {
        const bits=row.selected.map(p=>family.small.indexOf(p));
        if(bits.some(b=>b<0)||bits[0]===bits[1])throw new Error('Invalid pair');
        const mask=(1<<bits[0])|(1<<bits[1]);
        if(values.has(mask))throw new Error('Duplicate mask');
        values.set(mask,BigInt(row.survivalUpper));
      }
      return {values,inner:source.makeGraph(factor,family,outer)};
    },
    makeCorrection(state,weights) {
      const prior=source.makeCorrection(state.inner,weights);
      return (weight,mask,seen)=>{
        const old=prior(weight,mask,seen);
        const value=state.values.get(mask);
        if(value===undefined)return old;
        const next=base.ceilDiv(weight*value,base.scale);
        return old<next?old:next;
      };
    }
  };
}
if(require.main===module) {
  if(base.maxDivisor!==20000000||base.smallLimit!==73)throw new Error('Expected 20M/73 base');
  const [single,double,positive,negative]=process.argv.slice(4).map(read);
  if(positive.upper!==1000000000 || negative.upper!==1000000000)throw new Error('Unexpected linear cuts');
  const filtered=positiveTailGraph(positive,augmentDouble(double,augment(single)));
  const factors=new Map(negative.slopes.map(s=>[s.s,BigInt(s.factor)]));
  const result=combine(factors,base.maxDivisor,filtered);
  const num=BigInt(result.numeratorUpper.replace('.',''));
  const normalized=base.ceilDiv(num*979789013592184n,base.scale);
  console.log(result);
  console.log({normalizedNumerator:base.decimal(normalized),
    survivalRatioUpper:base.decimal(base.ceilDiv(normalized*base.scale,954160870567672n))});
}

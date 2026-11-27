// Compose a checked graph table with both linear families and the common singletons.
'use strict';
const fs=require('node:fs');
const base=require('./lagneau_crt_bound.cjs');
const wide=require('./lagneau_wide_graph.cjs');
const pos=require('./lagneau_extra_residue_one.cjs');
const neg=require('./lagneau_linear_tail.cjs');
const read=p=>JSON.parse(fs.readFileSync(p,'utf8'));

function main() {
  if(base.maxDivisor!==20000000 || base.smallLimit!==73)throw new Error('Expected the 20M/73 base');
  const graph=read(process.argv[4]||'Wide1B.json');
  const positive=read(process.argv[5]||'Positive1B.json');
  const negative=read(process.argv[6]||'lagneau_negative_1b.json');
  if(graph.B!==base.smallLimit || graph.cap<base.maxDivisor)throw new Error('Wrong graph table');
  for(const t of [positive,negative]) {
    if(t.maxDivisor!==base.maxDivisor || t.smallLimit!==base.smallLimit || t.upper!==1000000000) {
      throw new Error('Wrong conditional linear table');
    }
  }
  const factors=new Map(negative.slopes.map(row=>[row.s,BigInt(row.factor)]));
  const source=pos.positiveTailGraph(positive,wide.augment(graph));
  const recipe=neg.combine(factors,base.maxDivisor,source);
  console.log(recipe);
  const numerator=BigInt(recipe.numeratorUpper.replace('.',''));
  const denominator=954160870567672n;
  for (const [cutoff,multiplier] of [[1000000000,985858509556699n],[10000000000,979789013592184n]]) {
    const next=base.ceilDiv(numerator*multiplier,base.scale);
    console.log({cutoff,normalizedNumerator:base.decimal(next),
      upperRepresentedRatio:base.decimal(base.ceilDiv(next*base.scale,denominator))});
  }
}
if(require.main===module)main();

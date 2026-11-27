'use strict';

const assert=require('node:assert/strict');
const {distribution,jointUpper,hazardUnits,probabilityUnits}=require('./lagneau_joint_quantile.cjs');
const scale=10n**15n;
// Independent equally likely bits. On each side the broad and short rows
// overlap in one leaf, and the prior may use a short leaf when its gate closes.
const left=[[0,0,[7,8]],[2,1,[6,7]]], right=[[1,0,[10,11]],[3,1,[9,10]]];
const fraction=leaves=>1-2**(-new Set(leaves).size);
const risk=(rows,bits,gate,forced)=>Math.max(fraction(forced),...rows.map(([t,layer,leaves])=>
  ((bits>>t)&1) && (!layer || !(bits&(1<<gate))) ?
    fraction(layer?[...leaves,...forced]:leaves) : 0));
const alive=(rows,bits,gate,forced)=>forced.every(r=>!(bits&(1<<r))) &&
  rows.every(([t,layer,leaves])=>!(bits&(1<<t)) || (layer && Boolean(bits&(1<<gate))) ||
    leaves.every(r=>!(bits&(1<<r))));
const old=(bits,caseId)=>!((caseId&1 && bits&1 && bits&(1<<6)) ||
   (caseId&2 && bits&2 && bits&(1<<9)) || (caseId&4 && bits&4 && bits&8) ||
   (caseId&8 && bits&16 && bits&32));
const measure=n=>(BigInt(n)*scale+4095n)/4096n;
for(const mandatory of [[],[8]]) {
  const marginals=[new Map(),new Map()];
  for(let side=0;side<2;side++) {
    const risks=[];
    for(let low=0;low<64;low++)
      risks.push(risk(side?right:left,low,side,side?[]:mandatory));
    for(const h of risks)marginals[side].set(Math.floor(h*hazardUnits),
      Math.floor(probabilityUnits*risks.filter(y=>y>=h).length/64));
  }
  const leftLaw=distribution(marginals[0]), rightLaw=distribution(marginals[1]);
  for(let c=0;c<16;c++) {
    let prior=0,remaining=0;
    for(let bits=0;bits<4096;bits++)if(old(bits,c)) {
      prior++;
      if(alive(left,bits,0,mandatory) && alive(right,bits,1,[]))remaining++;
    }
    for(const p of [measure(prior),(scale+measure(prior))/2n,scale])
      assert.ok(measure(remaining)<=jointUpper(p,scale,leftLaw,rightLaw));
  }
}
console.log('Passed 32 twelve-coordinate models at three upper prior masses.');

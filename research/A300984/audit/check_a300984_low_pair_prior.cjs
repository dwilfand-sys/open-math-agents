'use strict';
// Verify that every exact two-small mask in the added low certificate takes
// the explicitly vertex-deleted Double1B graph bound in the existing driver.
const fs=require('node:fs'),path=require('node:path');
const base=require('./lagneau_crt_bound.cjs');
const {augment}=require('./lagneau_wide_graph.cjs');
const directory=process.argv[4];
if(base.maxDivisor!==20_000_000 || base.smallLimit!==73)throw Error('Unexpected baseline');
const read=name=>JSON.parse(fs.readFileSync(path.join(directory,name),'utf8'));
const original=augment(read('CertifiedEdgesTriples.json'));
const twoOuter=require('./lagneau_two_outer.cjs');
const pr=base.smallestPrimeFactors(2*base.maxDivisor);
const family=base.obstructionFamily(pr),state=original.makeGraph(pr,family,base.maxDivisor);
const maxVertex=state.core.primes.reduce((a,b)=>Math.max(a,b),0);
if(maxVertex>=400_000)throw Error('Unexpected old nonlinear vertex');
const rows=new Map(read('Double1B.json').rows.map(row=>[
  row.selected.reduce((v,t)=>v|(1<<family.small.indexOf(t)),0),BigInt(row.survivalUpper)]));
for(const first of [false,true]) {
  const prior=original.makeCorrection(state,r=>[r-1,r*(r-1)-1-(first?base.rootCount(r):0)]);
  const bare=twoOuter.makeCorrection(state.core,r=>[r-1,r*(r-1)-1-(first?base.rootCount(r):0)]);
  const passed=[],different=[],other=[];
  base.survivorUpper(family,first,(weight,mask,seen)=>{
    if(rows.has(mask)) {
      const a=prior(weight,mask,seen), b=base.ceilDiv(weight*rows.get(mask),base.scale);
      (b<=a?passed:different).push(family.small.filter((_,j)=>(mask&(1<<j))).join('*'));
    } else {
      const stripped=mask&(mask-1);
      if(stripped && !(stripped&(stripped-1))) {
        if(prior(weight,mask,seen)!==bare(weight,mask,seen))throw Error('Unexpected other pair prior');
        other.push(mask);
      }
    }
    return weight;
  });
  console.log(first?'first':'eligible','passed',passed.length,'failed',different.length,
    'exceptions',different.join(','));
  if(passed.length!==24 || different.length || other.length!==60)
    throw Error('Exact-pair prior condition failed');
  console.log('Other two-prime masks:',other.length,'old maximum graph vertex:',maxVertex);
}

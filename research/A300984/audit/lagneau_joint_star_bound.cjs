'use strict';

const {ceilDiv, scale} = require('./lagneau_crt_bound.cjs');

// Original star rows use high primes >14,000,000. Larger centers use high
// primes >4,000,000 on the event that all free medium primes <=250 are absent.
// A previous nonlinear divisor <=10^9 containing such a high prime needs a
// second active medium prime <250, hence vanishes on the gate.
function jointStars(rows, layers, previous, positive=false, extra={}) {
  const byFilter=new Map(), merged=new Map();
  for(const [data,layer,extension] of [[rows,false,false],[layers,true,false],[extra.rows||[],false,true]]) {
    for(const raw of data) {
      const multiplier=raw.multiplier||1, t=raw.slope;
      if((extension ? t<=10_000 : layer ? t<=1000 : (t<=73 || t>1000)) ||
         raw.lower!==(layer?4_000_000:14_000_000) ||
         raw.upper!==(layer||extension?100_000_000:1_000_000_000) ||
         t*multiplier%6!==(positive?1:5)) throw Error('Unexpected star row');
      const key=multiplier+':'+(raw.small||0);
      if(!byFilter.has(key))byFilter.set(key,[]);
      byFilter.get(key).push({t,layer,short:layer||extension,factor:BigInt(raw.factor)});
    }
  }
  return {
    makeGraph(factor,family,outer) {
      const negative=[],positiveBits=[13,43,61,67,73].map(s=>1<<family.small.indexOf(s));
      for(let i=0;i<family.small.length;i++)
        if(family.small[i]%6===5)negative.push([family.small[i],1<<i]);
      const gate=[];
      for(let t=74;t<=250;t++)
        if(t%6===(positive?1:5) && factor[t]===t && factor[2*t-1]!==2*t-1)gate.push(t);
      for(const list of byFilter.values())for(const {t} of list)
        if(factor[t]!==t || factor[2*t-1]===2*t-1) throw Error('Invalid center');
      return {core:previous.makeGraph(factor,family,outer),small:family.small,
        negative,positiveBits,gate,gateSet:new Set(gate)};
    },
    makeCorrection(state,weights) {
      const before=previous.makeCorrection(state.core,weights);
      return (weight,mask,seen)=>{
        const prior=before(weight,mask,seen), marker=mask+1;
        const least=state.negative.find(([,bit])=>(mask&bit)!==0);
        const required=least?least[0]:0;
        const filter=positive?state.positiveBits.reduce((v,bit,i)=>v+((mask&bit)?1<<i:0),0):required;
        const group=required+':'+filter;
        if(!merged.has(group)) {
          const standard=byFilter.get('1:'+filter)||[];
          const mixed=byFilter.get(required+':'+filter)||[];
          const all=[...standard,...mixed].sort((a,b)=>a.factor<b.factor?-1:a.factor>b.factor?1:0);
          if(new Set(all.map(row=>row.t)).size!==all.length)throw Error('Duplicate active center');
          merged.set(group,all);
        }
        let ordered=merged.get(group).filter(({t})=>seen[t]!==marker);
        // A mandatory row in this leaf sign and mask is always triggered,
        // even where its high coordinates overlap those of a medium star.
        if(extra.mandatory) {
          const f=BigInt(extra.mandatory(mask,state.small));
          if(f<0n || f>scale)throw Error('Bad mandatory star factor');
          if(f<scale) {
            // Short stars use only leaves <=100m. The mandatory test uses
            // only leaves >100m, so both conditional survival factors multiply.
            ordered=ordered.map(row=>row.short ? {...row,factor:ceilDiv(row.factor*f,scale)} : row)
              .sort((a,b)=>a.factor<b.factor?-1:a.factor>b.factor?1:0);
            const at=ordered.findIndex(r=>r.factor>f);
            ordered.splice(at<0?ordered.length:at,0,{always:true,factor:f});
          }
        }
        let noOldUpper=scale, noLargeUpper=scale, noOldOrGateLower=scale, loss=0n;
        const marginal=extra.quantile?.marginal({weight,mask,prior,required,positive,
          mixed:byFilter.has(required+':'+filter)});
        for(const t of state.gate)if(seen[t]!==marker)
          noOldOrGateLower=noOldOrGateLower*BigInt(t-2)/BigInt(t-1);
        for(let i=0;i<ordered.length;i++) {
          const row=ordered[i], t=BigInt(row.t||1);
          if(row.always) {noOldUpper=0n;noOldOrGateLower=0n;}
          else if(row.layer)noLargeUpper=ceilDiv(noLargeUpper*(t-1n),t);
          else {
            noOldUpper=ceilDiv(noOldUpper*(t-1n),t);
            if(!state.gateSet.has(row.t))noOldOrGateLower=noOldOrGateLower*(t-2n)/(t-1n);
          }
          const width=(i+1===ordered.length?scale:ordered[i+1].factor)-row.factor;
          if(!width)continue;
          const none=noOldUpper-noOldOrGateLower*(scale-noLargeUpper)/scale;
          if(marginal)marginal.record(scale-row.factor,scale-none);
          const noTest=ceilDiv(weight*none,scale);
          if(prior>noTest)loss+=(prior-noTest)*width/scale;
        }
        const result=prior-loss;
        return marginal?marginal.finish(result):result;
      };
    }
  };
}
module.exports={jointStars};

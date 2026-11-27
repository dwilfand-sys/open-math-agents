'use strict';

const {ceilDiv, scale} = require('./lagneau_crt_bound.cjs');

function mediumStars(rows, previous, positive=false, gateCutoff=0) {
  const bySmall=new Map();
  const lower=gateCutoff?4_000_000:14_000_000, upper=gateCutoff?100_000_000:1_000_000_000;
  for (const row of rows) {
    if (row.slope<=Math.max(73,gateCutoff) || row.slope%6!==(positive?1:5) || row.lower!==lower || row.upper!==upper)
      throw Error('Unexpected medium-prime range');
    const small=row.small || 0;
    if (!bySmall.has(small)) bySmall.set(small,[]);
    bySmall.get(small).push(row);
  }
  for(const entries of bySmall.values()) {
    entries.sort((a,b)=>BigInt(a.factor)<BigInt(b.factor)?-1:BigInt(a.factor)>BigInt(b.factor)?1:0);
    if(new Set(entries.map(r=>r.slope)).size!==entries.length) throw Error('Repeated medium prime');
  }
  return {
    makeGraph(factor,family,outer) {
      const smallSlopes=[], positiveBits=[13,43,61,67,73].map(s=>1<<family.small.indexOf(s));
      for (let k=0; k<family.small.length; ++k) {
        if (family.small[k]%6===5) smallSlopes.push([family.small[k],1<<k]);
      }
      for (const row of rows) {
        if (factor[row.slope]!==row.slope) throw Error('Medium center is composite');
        if (positive && factor[2*row.slope-1]===2*row.slope-1) throw Error('Forbidden singleton center');
      }
      const gatePrimes=[];
      for(let r=74;r<=gateCutoff;r++) if(factor[r]===r && factor[2*r-1]!==2*r-1) gatePrimes.push(r);
      return {core:previous.makeGraph(factor,family,outer),smallSlopes,positiveBits,gatePrimes};
    },
    makeCorrection(state,weights) {
      const inner = previous.makeCorrection(state.core,weights);
      return (weight,mask,seen) => {
        const prior = inner(weight,mask,seen);
        const least=state.smallSlopes.find(([s,bit])=>(mask&bit)!==0);
        const key=positive
          ? state.positiveBits.reduce((v,bit,i)=>v+((mask&bit)?(1<<i):0),0)
          : least?least[0]:0;
        const candidates=bySmall.get(key);
        if (!candidates) return prior;
        const ordered=candidates.filter(r=>seen[r.slope]!==mask+1);
        let gate=scale;
        for(const r of state.gatePrimes) if(seen[r]!==mask+1) gate=gate*BigInt(r-2)/BigInt(r-1);
        let none=gateCutoff?scale:weight, loss=0n;
        for (let i=0; i<ordered.length; ++i) {
          const {slope,factor} = ordered[i], t=BigInt(slope);
          none=ceilDiv(none*(t-1n),t);
          const next=i+1<ordered.length ? BigInt(ordered[i+1].factor) : scale;
          const width=next-BigInt(factor);
          if (width<0n) throw Error('Bad survival-factor ordering');
          const noTestWeight=gateCutoff
            ? ceilDiv(weight*(scale-gate*(scale-none)/scale),scale) : none;
          if (prior>noTestWeight) loss+=(prior-noTestWeight)*width/scale;
        }
        return prior-loss;
      };
    }
  };
}

module.exports = {mediumStars};

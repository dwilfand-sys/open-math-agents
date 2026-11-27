'use strict';

const {ceilDiv, scale} = require('./lagneau_crt_bound.cjs');

function mediumStars(rows, previous) {
  const bySmall=new Map();
  for (const row of rows) {
    if (row.slope<=73 || row.slope%6!==5 || row.lower!==14_000_000 || row.upper!==1_000_000_000)
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
      const smallSlopes=[];
      for (let k=0; k<family.small.length; ++k) {
        if (family.small[k]%6===5) smallSlopes.push([family.small[k],1<<k]);
      }
      for (const row of rows)
        if (factor[row.slope]!==row.slope) throw Error('Medium center is composite');
      return {core:previous.makeGraph(factor,family,outer),smallSlopes};
    },
    makeCorrection(state,weights) {
      const inner = previous.makeCorrection(state.core,weights);
      return (weight,mask,seen) => {
        const prior = inner(weight,mask,seen);
        const least=state.smallSlopes.find(([s,bit])=>(mask&bit)!==0);
        const candidates=bySmall.get(least?least[0]:0);
        if (!candidates) return prior;
        const ordered=candidates.filter(r=>seen[r.slope]!==mask+1);
        let none=weight, loss=0n;
        for (let i=0; i<ordered.length; ++i) {
          const {slope,factor} = ordered[i], t=BigInt(slope);
          none=ceilDiv(none*(t-1n),t);
          const next=i+1<ordered.length ? BigInt(ordered[i+1].factor) : scale;
          const width=next-BigInt(factor);
          if (width<0n) throw Error('Bad survival-factor ordering');
          if (prior>none) loss+=(prior-none)*width/scale;
        }
        return prior-loss;
      };
    }
  };
}

module.exports = {mediumStars};

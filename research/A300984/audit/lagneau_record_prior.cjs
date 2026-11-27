'use strict';
const fs=require('node:fs');
function create(name){
  const previous=new Map();let centers=[];
  const target=fs.openSync(name,'w');
  function source(core) {
    return {
      makeGraph(factor,family,outer) {
        centers=[];
        for(let t=74;t<=50_000;t++)if(factor[t]===t && factor[2*t-1]!==2*t-1)centers.push(t);
        fs.writeSync(target,JSON.stringify({small:family.small,centers})+'\n');
        return core.makeGraph(factor,family,outer);
      },
      makeCorrection(state,weights) {
        const correct=core.makeCorrection(state,weights);
        return (weight,mask,seen)=>{
          const upper=correct(weight,mask,seen);
          previous.set(mask,upper);
          return upper;
        };
      }
    };
  }
  function result(core) {
    return {
      makeGraph(factor,family,outer){return core.makeGraph(factor,family,outer);},
      makeCorrection(state,weights) {
        const correct=core.makeCorrection(state,weights);
        const first=weights(5)[1]===17;
        return (weight,mask,seen)=>{
          const upper=correct(weight,mask,seen);
          const blocked=centers.filter(t=>seen[t]===mask+1);
          fs.writeSync(target,JSON.stringify({first,mask,weight:String(weight),old:String(previous.get(mask)),
            upper:String(upper),blocked})+'\n');
          return upper;
        };
      }
    };
  }
  return {source,result};
}
module.exports={create};

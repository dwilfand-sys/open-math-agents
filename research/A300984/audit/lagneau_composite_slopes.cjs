'use strict';

const fs=require('node:fs');
const {scale,ceilDiv}=require('./lagneau_crt_bound.cjs');
const guards={1:[13,43,61,67,73],5:[5,11,17,23,29,41,47,53,59,71]};
const pairs=[[5,13],[5,17],[11,13],[5,29],[5,43],[13,17],[5,47],[11,23],
  [5,53],[5,59],[13,23],[5,61],[11,29],[5,67],[5,73],[13,29],[17,23],
  [11,41],[11,43],[17,29],[13,41],[11,53],[13,47],[23,29]];

function remainingPairs() {
  const small=[...guards[1],...guards[5]].sort((a,b)=>a-b), used=new Set(pairs.map(p=>p.join(',')));
  const rest=[];
  for(const a of small)for(const b of small)if(a<b && !used.has(a+','+b)) {
    const n=2*a*b-1;
    for(let d=2;d*d<=n;d++)if(n%d===0){rest.push([a,b]);break;}
  }
  if(rest.length!==60)throw Error('Incomplete supplementary pair set');
  return rest;
}

function read(path,sign,lower,upper,remaining=false) {
  const bytes=fs.readFileSync(path);
  const lines=(path.endsWith('.gz')?require('node:zlib').gunzipSync(bytes):bytes)
    .toString('utf8').trim().split(/\r?\n/);
  if(lines.shift()!==`# ${sign} ${lower} ${upper}${remaining?' remaining':''}` || !guards[sign])
    throw Error('Wrong composite slope table');
  const active=guards[sign], cards=1<<active.length;
  const factors=new Map(), eligible=(remaining?remainingPairs():pairs).filter(([a,b])=>a*b%6===sign);
  for(const [a,b] of eligible)factors.set(a+','+b,Array(cards));
  for(const line of lines){
    const [a,b,k,count,f]=line.split(/\s+/), row=factors.get(a+','+b);
    const guard=Number(k),value=BigInt(f);
    if(!row || !Number.isInteger(guard) || guard<0 || guard>=cards ||
       row[guard]!==undefined || Number(count)<0 || value<=0n || value>scale)
      throw Error('Malformed composite slope cell');
    row[guard]=value;
  }
  for(const [a,b] of eligible) {
    const required=active.reduce((v,p,j)=>(p===a||p===b)?v|(1<<j):v,0);
    const row=factors.get(a+','+b);
    for(let k=0;k<cards;k++)if((row[k]!==undefined)!==((k&required)===required))
      throw Error('Missing or unexpected guard mask');
  }
  return {sign,lower,upper,factors,eligible};
}

function merge(first,second) {
  if(first.sign!==second.sign || first.lower!==second.lower || first.upper!==second.upper)
    throw Error('Composite tables for different coordinate ranges');
  const factors=new Map([...first.factors,...second.factors]);
  if(factors.size!==first.factors.size+second.factors.size)throw Error('Repeated factor pair');
  return {...first,factors,eligible:[...first.eligible,...second.eligible]};
}

function callback(table) {
  let bits, rowMasks, original;
  const cache=new Map();
  return (mask,small)=>{
    if(!bits) {
      const toBit=p=>{
        const i=small.indexOf(p);
        if(i<0)throw Error('Incompatible small-prime assignment');
        return 1<<i;
      };
      original=small.join(',');
      bits=guards[table.sign].map(toBit);
      rowMasks=table.eligible.map(([a,b])=>[toBit(a)|toBit(b),table.factors.get(a+','+b)]);
    } else if(original!==small.join(','))throw Error('Changed small-prime order');
    if(cache.has(mask))return cache.get(mask);
    const guard=bits.reduce((v,b,j)=>(mask&b)?v|(1<<j):v,0);
    let best=scale;
    for(const [needed,row] of rowMasks)if((needed&mask)===needed && row[guard]<best)
      best=row[guard];
    cache.set(mask,best);
    return best;
  };
}

function extend(tables,previous) {
  for(const sign of [1,5]) {
    let end=0;
    for(const table of tables.filter(t=>t.sign===sign).sort((a,b)=>a.lower-b.lower)) {
      const low=table.lower>=50_000 && table.upper<=4_000_000;
      const high=table.lower>=3_000_000_000 && table.upper<=10_000_000_000;
      if(table.lower<end || !(low||high) || table.upper<=table.lower)
        throw Error('Overlapping composite intervals or star high range');
      end=table.upper;
    }
  }
  const factors=tables.map(t=>({exact:t.lower<400_000,value:callback(t)}));
  return {
    makeGraph(primes,family,outer) {
      return {small:family.small,before:previous.makeGraph(primes,family,outer)};
    },
    makeCorrection(state,weights) {
      const old=previous.makeCorrection(state.before,weights);
      return (weight,mask,seen)=>{
        let upper=old(weight,mask,seen);
        const minusOne=mask&(mask-1),atMostTwo=(minusOne&(minusOne-1))===0;
        for(const {exact,value} of factors)if(!exact || atMostTwo)
          upper=ceilDiv(upper*value(mask,state.small),scale);
        return upper;
      };
    }
  };
}
function product(callbacks) {
  return (mask,small)=>callbacks.reduce((v,f)=>ceilDiv(v*f(mask,small),scale),scale);
}
module.exports={read,callback,extend,product,merge};

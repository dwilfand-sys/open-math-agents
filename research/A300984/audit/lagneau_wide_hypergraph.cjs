// Include distinct two- and three-large-prime obstructions in the same Janson bound.
'use strict';
const {makeInputs}=require('./lagneau_wide_graph.cjs');
const S=100000000, s=BigInt(S), scale=10n**15n;
function exact(n) {
  if(!Number.isSafeInteger(n)||n<0)throw new Error('Integer overflow');
  return BigInt(n);
}
function expBound(n,d) {
  if(n<=0n)return scale;
  let num=1n,den=1n,p=1n;
  for(let j=1n;j<=6n;j++){p*=n;num=num*d*j+p;den*=d*j;}
  return (scale*den+num-1n)/num;
}
function upperIndex(v,max) {
  let lo=0,hi=v.length;
  while(lo<hi) {
    const mid=(lo+hi)>>>1;
    if(v[mid]<=max)lo=mid+1;
    else hi=mid;
  }
  return lo;
}
function bound(inputs,D,B,t) {
  const {isPrime,vertices}=inputs;
  if(t && (!isPrime(t)||t>B||isPrime(2*t-1)))throw new Error('Invalid small prime');
  const v=Uint32Array.from(t?vertices.filter(r=>!isPrime(2*t*r-1)):vertices);
  const l=Uint32Array.from(v,q=>Math.floor(S/q));
  const u=Uint32Array.from(v,q=>Math.ceil(S/(q-1)));
  for(let i=0;i<v.length;i++)if(l[i]*v[i]>S||u[i]*(v[i]-1)<S)throw new Error('Rounding');
  const prefixes=[],after=[];
  let storage=0;
  for(let i=0;i<v.length;i++){
    const maxj=upperIndex(v,Math.floor(D/((B+1)*v[i])));
    if(maxj<=i+1)break;
    prefixes.push(storage);after.push(maxj);
    storage+=maxj-i-1;
  }
  const graphPair=new Uint8Array(storage);
  const extension=new Float64Array(storage),extensionSq=new Float64Array(storage);
  const graphSum=new Float64Array(v.length),graphSq=new Float64Array(v.length);
  const tripleSum=new Float64Array(v.length);
  function usable(d) {return isPrime(2*d-1)||(t!==0&&t*d<=D&&isPrime(2*t*d-1));}
  let edges=0,triples=0,edgeFirst=0,tripleFirst=0n;
  for(let i=0;i<v.length&&v[i]*v[i]<D;i++){
    const hi=upperIndex(v,Math.floor(D/v[i]));
    for(let j=i+1;j<hi;j++){
      if(!usable(v[i]*v[j]))continue;
      edges++;edgeFirst+=l[i]*l[j];
      graphSum[i]+=u[j];graphSum[j]+=u[i];
      graphSq[i]+=u[j]*u[j];graphSq[j]+=u[i]*u[i];
      if(i<after.length&&j<after[i])graphPair[prefixes[i]+j-i-1]=1;
    }
  }
  function pairUpdate(i,j,x) {
    if(i>=after.length||j>=after[i])throw new Error('Unindexed triple pair');
    const k=prefixes[i]+j-i-1;
    extension[k]+=x;extensionSq[k]+=x*x;
  }
  for(let i=0;i<v.length&&v[i]**3<D;i++) {
    for(let j=i+1;j<v.length&&v[i]*v[j]*v[j]<D;j++) {
      const p=v[i]*v[j], hi=upperIndex(v,Math.floor(D/p));
      let sumL=0;
      for(let k=j+1;k<hi;k++){
        if(!usable(p*v[k]))continue;
        triples++;sumL+=l[k];
        tripleSum[i]+=u[j]*u[k];tripleSum[j]+=u[i]*u[k];tripleSum[k]+=u[i]*u[j];
        pairUpdate(i,j,u[k]);pairUpdate(i,k,u[j]);pairUpdate(j,k,u[i]);
      }
      if(sumL)tripleFirst+=BigInt(l[i])*BigInt(l[j])*exact(sumL);
    }
  }
  let vertexStars=0n,pairStars=0n;
  for(let i=0;i<v.length;i++) {
    const rest=exact(graphSum[i])*s+exact(tripleSum[i]);
    // Remove the graph's self-pairs. Keeping the nonnegative triple
    // self-pairs produces a valid upper bound on the intersections.
    vertexStars+=BigInt(u[i])*(rest*rest-s*s*exact(graphSq[i]));
  }
  for(let i=0;i<after.length;i++){
    for(let j=i+1;j<after[i];j++){
      const id=prefixes[i]+j-i-1;
      if(!extension[id])continue;
      const nx=exact(extension[id]);
      const term=2n*BigInt(graphPair[id])*s*nx+nx*nx-exact(extensionSq[id]);
      pairStars+=BigInt(u[i])*BigInt(u[j])*term;
    }
  }
  // Distinct sets can share one or two vertices. Summing the vertex
  // intersections and all pair intersections is conservative when two
  // vertices are shared. The two denominators are respectively S^5,S^4.
  const num=2n*exact(edgeFirst)*s**3n+2n*tripleFirst*s*s-vertexStars-pairStars*s;
  const upper=expBound(num,2n*s**5n);
  return {small:t,vertices:v.length,edges,triples,lowerEdgeFirst:String(edgeFirst),
    lowerTripleFirst:String(tripleFirst),upperVertexStars:String(vertexStars),
    upperPairStars:String(pairStars),survivalUpper:String(upper)};
}
module.exports={bound};
if(require.main===module) {
  const D=Number(process.argv[2]||1000000000),B=Number(process.argv[3]||73);
  const inputs=makeInputs(D,B);
  const small=process.argv[5]?process.argv[5].split(',').map(Number):[0];
  if(!process.argv[5])for(let q=5;q<=B;q++)if(inputs.isPrime(q)&&!inputs.isPrime(2*q-1))small.push(q);
  const rows=[];
  for(const t of small){const a=bound(inputs,D,B,t);rows.push(a);console.log(t,a.edges,a.triples,a.survivalUpper);}
  if(process.argv[4])require('node:fs').writeFileSync(process.argv[4],JSON.stringify(
    {cap:D,B,precision:S,rows},null,2)+'\n');
}

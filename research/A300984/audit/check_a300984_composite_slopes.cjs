'use strict';

// Independent complementary-factor sieve and direct summation of admissible
// signatures. The C# generator solves for the factor index and uses a zeta sum.
const fs=require('node:fs');
const scale=10n**15n,width=262144;
function replay(path,input) {
  let bytes=input===undefined?fs.readFileSync(path):Buffer.from(input,'utf8');
  if(path.endsWith('.gz'))bytes=require('node:zlib').gunzipSync(bytes);
  const lines=bytes.toString('utf8').trim().split(/\r?\n/);
  const [_,sign,lower,upper]=lines.shift().split(' ').map(Number);
  const small=sign===5?[5,11,17,23,29,41,47,53,59,71]:[13,43,61,67,73];
  const cards=1<<small.length, rejected=cards;
  const rows=new Map();
  for(const line of lines) {
    const [a,b,g,n,f]=line.split(' '), c=a*b;
    if(!rows.has(c))rows.set(c,{needed:small.reduce((m,t,j)=>
      t===Number(a)||t===Number(b)?m|(1<<j):m,0),data:new Map()});
    rows.get(c).data.set(Number(g),[Number(n),BigInt(f)]);
  }
  const limit=Math.ceil(Math.sqrt(2*upper*Math.max(...rows.keys())));
  const mark=new Uint8Array(limit+1),primes=[];
  for(let p=2;p<=limit;p++)if(!mark[p]) {
    primes.push(p);
    for(let k=p*p;k<=limit;k+=p)mark[k]=1;
  }
  const first=Math.floor((lower-sign)/6)+1,end=Math.floor((upper-sign)/6)+1;
  function inverse(x,n) {
    let t=0,u=1,a=n,b=x%n;
    while(b){const k=Math.floor(a/b);[a,b]=[b,a-k*b];[t,u]=[u,t-k*u];}
    return a===1?(t%n+n)%n:null;
  }
  function makeForm(m,b) {
    const qs=[],offsets=[], bottom=m*first+b,top=m*(end-1)+b;
    for(const q of primes) {
      if(q*q>top)break;
      const inv=inverse(q,m);
      if(inv===null){if(b%q===0)throw Error('Bad form');continue;}
      const want=b*inv%m;
      let other=Math.ceil(bottom/q);
      other+=(want-other%m+m)%m;
      const j=(q*other-b)/m-first;
      if(!Number.isSafeInteger(j)||j<0||j>=q)throw Error('Bad complementary factor');
      qs.push(q);offsets.push(j);
    }
    if(bottom<=Math.sqrt(top))throw Error('Small exceptional prime');
    return {qs:Uint32Array.from(qs),offsets:Uint32Array.from(offsets)};
  }
  const flags=new Uint8Array(width),labels=new Uint16Array(width);
  function sieve({qs,offsets},n) {
    flags.fill(0,0,n);
    for(let i=0;i<qs.length;i++){
      let j=offsets[i];
      for(;j<n;j+=qs[i])flags[j]=1;
      offsets[i]=j-n;
    }
  }
  const rform=makeForm(6,sign);
  const singleton=sign===1?makeForm(12,1):null;
  const guards=small.map(t=>makeForm(12*t,2*sign*t-1));
  for(const [c,row] of rows) {
    row.form=makeForm(12*c,2*sign*c-1);
    row.totals=Array(cards).fill(0);
    row.factors=Array(cards).fill(scale);
  }
  const hist=new Uint32Array(cards),counts=new Uint32Array(cards);
  for(let start=first;start<end;start+=width) {
    const n=Math.min(end-start,width), top=BigInt(6*(start+n-1)+sign);
    sieve(rform,n);
    for(let j=0;j<n;j++)labels[j]=flags[j]?rejected:0;
    if(singleton) {
      sieve(singleton,n);
      for(let j=0;j<n;j++)if(!flags[j])labels[j]=rejected;
    }
    for(let k=0;k<guards.length;k++) {
      sieve(guards[k],n);
      for(let j=0;j<n;j++)if(flags[j])labels[j]|=1<<k;
    }
    for(const [c,row] of rows) {
      sieve(row.form,n);
      hist.fill(0); counts.fill(0);
      for(let j=0;j<n;j++)if(!flags[j] && labels[j]<rejected &&
        (upper>4_000_000 || c*(6*(start+j)+sign)>20_000_000))hist[labels[j]]++;
      for(let code=0;code<cards;code++) {
        if(!hist[code] || (code&row.needed)!==row.needed)continue;
        const optional=code^row.needed;
        for(let bits=optional;;bits=(bits-1)&optional) {
          counts[bits|row.needed]+=hist[code];
          if(!bits)break;
        }
      }
      for(const k of row.data.keys()) {
        row.totals[k]+=counts[k];
        const den=top+BigInt(counts[k]);
        row.factors[k]=(row.factors[k]*top+den-1n)/den;
      }
    }
  }
  let cells=0;
  for(const [c,row] of rows)for(const [k,[n,f]] of row.data) {
    if(row.totals[k]!==n || row.factors[k]!==f)throw Error('Mismatch at '+c+','+k);
    cells++;
  }
  console.log(path,rows.size,cells,'cells passed');
}
module.exports={replay};
if(require.main===module)for(const path of process.argv.slice(2))replay(path);

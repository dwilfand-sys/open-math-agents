'use strict';
// Independent replay. Solve for the complementary factor of each composite
// linear value and retain the common high-prime eligibility labels once.
const fs=require('node:fs');
const source=process.argv[2], positive=process.argv[3]==='positive';
const slopes=positive?[13,43,61,67,73]:[5,11,17,23,29,41,47,53,59,71];
const residue=positive?1:5, lower=14_000_000, upper=1_000_000_000, block=262144;
const first=Math.floor((lower-residue)/6)+1, end=Math.floor((upper-residue)/6)+1;
const size=end-first, rejected=1<<slopes.length, scale=10n**15n;
const rows=fs.readFileSync(source,'utf8').trim().split('\n').map(line=>line.trim().split(/\s+/));
const centers=[...new Set(rows.map(row=>Number(row[0])))];
const limit=Math.ceil(Math.sqrt(2*Math.max(...centers)*upper));
const markedBase=new Uint8Array(limit+1), primes=[];
for(let q=2;q<=limit;q++) if(!markedBase[q]) {
  primes.push(q);
  for(let x=q*q;x<=limit;x+=q) markedBase[x]=1;
}
function inverse(x,m) {
  let a=x,b=m,s=1,t=0;
  while(b) {
    const k=Math.floor(a/b);
    [a,b]=[b,a-k*b]; [s,t]=[t,s-k*t];
  }
  return a===1?(s%m+m)%m:null;
}
function progression(m,c) {
  const qs=[], next=[];
  const lowValue=m*first+c, maxValue=m*(end-1)+c;
  for(const q of primes) {
    if(q*q>maxValue) break;
    const inv=inverse(q,m);
    if(inv===null) {
      if(c%q===0) throw Error('Nonprimitive form');
      continue;
    }
    const target=(c*inv)%m;
    let cofactor=Math.ceil(lowValue/q);
    cofactor+=(target-cofactor%m+m)%m;
    const index=(q*cofactor-c)/m-first;
    if(!Number.isSafeInteger(index) || index<0 || index>=q) throw Error('Invalid first multiple');
    qs.push(q); next.push(index);
  }
  if(lowValue<=primes.at(-1)) throw Error('Small-prime exceptional case');
  return [Uint32Array.from(qs),Uint32Array.from(next)];
}
const flags=new Uint8Array(block);
function sieve(form,base,n) {
  flags.fill(0,0,n);
  const [qs,next]=form;
  for(let i=0;i<qs.length;i++) {
    let j=next[i]-base;
    for(;j<n;j+=qs[i]) flags[j]=1;
    next[i]=base+j;
  }
}
const labels=new Uint16Array(size);
const rForm=progression(6,residue);
const singleton=positive?progression(12,1):null;
const smallForms=slopes.map(s=>progression(12*s,2*s*residue-1));
for(let start=0;start<size;start+=block) {
  const n=Math.min(block,size-start);
  sieve(rForm,start,n);
  for(let i=0;i<n;i++) if(flags[i]) labels[start+i]=rejected;
  if(positive) {
    sieve(singleton,start,n);
    for(let i=0;i<n;i++) if(!flags[i]) labels[start+i]=rejected;
  }
  for(let j=0;j<slopes.length;j++) {
    sieve(smallForms[j],start,n);
    for(let i=0;i<n;i++) if(flags[i]) labels[start+i]|=1<<j;
  }
}
const expected=new Map(rows.map(([t,s,n,f])=>[t+','+s,[Number(n),BigInt(f)]]));
for(const t of centers) {
  const form=progression(12*t,2*t*residue-1);
  const keys=positive?Array.from({length:rejected},(_,i)=>i):[0,...slopes];
  const counts=keys.map(()=>0), factors=keys.map(()=>scale);
  for(let start=0;start<size;start+=block) {
    const n=Math.min(block,size-start);
    sieve(form,start,n);
    const h=new Uint32Array(rejected);
    for(let i=0;i<n;i++) if(!flags[i] && labels[start+i]<rejected) h[labels[start+i]]++;
    const top=BigInt(6*(first+start+n-1)+residue);
    for(let j=0;j<keys.length;j++) {
      const wanted=positive?keys[j]:j?1<<(j-1):0;
      let count=0;
      // Direct summation of the compatible disjoint signatures.
      for(let mask=wanted;mask<rejected;mask=(mask+1)|wanted) count+=h[mask];
      counts[j]+=count;
      const d=top+BigInt(count);
      factors[j]=(factors[j]*top+d-1n)/d;
    }
  }
  for(let j=0;j<keys.length;j++) {
    const [n,f]=expected.get(t+','+keys[j]);
    if(n!==counts[j] || f!==factors[j]) throw Error('Mismatch at '+t+','+keys[j]);
  }
  console.log(t,keys.length);
}

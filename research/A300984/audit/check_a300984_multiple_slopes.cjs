'use strict';
// Independently replay the complete census using complementary cofactors and
// prime, rather than composite, signatures of the ten shifted forms.
const fs=require('node:fs');
const source=process.argv[2], data=fs.readFileSync(source);
const plain=source.endsWith('.gz')?require('node:zlib').gunzipSync(data):data;
const rows=plain.toString('utf8').trim().split('\n').map(x=>x.trim().split(/\s+/));
const lower=Number(rows[0][0]),upper=Number(rows[0][1]);
const width=262144, scale=10n**15n, slopes=[5,11,17,23,29,41,47,53,59,71];
const size=1<<slopes.length, full=size-1;
if(rows.length!==size || lower<10000 || upper<=lower || upper>1e11)throw Error('Invalid census');
const first=Math.floor((lower-5)/6)+1,end=Math.floor((upper-5)/6)+1;
const cap=Math.ceil(Math.sqrt(2*slopes.at(-1)*upper));
if(lower<=cap)throw Error('Small prime exceptional range');
const primeList=[], bad=new Uint8Array(cap+1);
for(let q=2;q<=cap;q++)if(!bad[q]){
  primeList.push(q);
  for(let x=q*q;x<=cap;x+=q)bad[x]=1;
}
function inverse(x,m) {
  let a=x,b=m,u=1,v=0;
  while(b) {
    const k=Math.floor(a/b);
    [a,b]=[b,a%b]; [u,v]=[v,u-k*v];
  }
  return a===1?(u%m+m)%m:null;
}
function form(m,c) {
  const steps=[],offset=[];
  const low=m*first+c,max=m*(end-1)+c;
  for(const q of primeList) {
    if(q*q>max)break;
    const inv=inverse(q,m);
    if(inv===null){if(c%q===0)throw Error('Nonprimitive form');continue;}
    const w=Math.ceil(low/q);
    const cofactor=w+((c*inv%m-w%m+m)%m);
    const index=(q*cofactor-c)/m-first;
    if(!Number.isSafeInteger(index)||index<0||index>=q)throw Error('Invalid cofactor');
    steps.push(q);offset.push(index);
  }
  return [Uint32Array.from(steps),Uint32Array.from(offset)];
}
function mark([qs,next],flags,len) {
  flags.fill(0,0,len);
  for(let i=0;i<qs.length;i++) {
    const q=qs[i];let j=next[i];
    for(;j<len;j+=q)flags[j]=1;
    next[i]=j-len;
  }
}
const rForm=form(6,5), forms=slopes.map(s=>form(12*s,10*s-1));
const rBad=new Uint8Array(width), flags=new Uint8Array(width), signature=new Uint16Array(width);
const factors=Array(size).fill(scale), totals=new Float64Array(size), h=new Uint32Array(size);
for(let k=first;k<end;k+=width) {
  const len=Math.min(end-k,width);
  mark(rForm,rBad,len);
  signature.fill(0,0,len);
  for(let j=0;j<forms.length;j++) {
    mark(forms[j],flags,len);
    for(let i=0;i<len;i++)if(!flags[i])signature[i]|=1<<j;
  }
  h.fill(0);for(let i=0;i<len;i++)if(!rBad[i])h[signature[i]]++;
  for(let bit=1;bit<size;bit*=2)
    for(let m=0;m<size;m++)if(m&bit)h[m]+=h[m^bit];
  const top=BigInt(6*(k+len-1)+5);
  for(let m=1;m<size;m++){
    const ct=h[full^(m&-m)]-h[full^m];
    if(ct===0)continue;
    totals[m]+=ct;const d=top+BigInt(ct);
    factors[m]=(factors[m]*top+d-1n)/d;
  }
}
for(let i=0;i<size;i++) {
  const [a,b,m,c,f]=rows[i];
  if(Number(a)!==lower||Number(b)!==upper||Number(m)!==i||
      Number(c)!==totals[i]||BigInt(f)!==factors[i])throw Error('Mismatch at '+i);
}
console.log('Verified all',size,'masks at',lower,upper);

/* A single Kronecker product tests the 101-representation threshold for
 * 10,065,379 consecutive integers. Codex for @dwilfand-sys, 2026-11-28.
 * Run: node packed_101_guard.js
 *
 * Set B=1024. Encode the positive squarefree indicators as S(B), and
 * encode Q(B)=sum_{1<=k<=503} B^(k^2). Every coefficient of S*Q is at
 * most 503, so its base-B digits equal the ordinary representation counts
 * with the specified 503 roots. Adding 411 per lane puts the 512-bit on
 * exactly when that count is at least 101. Even the largest possible sum
 * 503+411 stays within a single lane.
 */
"use strict";

const assert = require("node:assert/strict");

function packedProduct(low,high,maximumRoot) {
  const sf = new Uint8Array(high+1).fill(1,1);
  for(let d=2;d*d<=high;d++) {
    const q=d*d;
    for(let t=q;t<=high;t+=q) sf[t]=0;
  }
  function pack(bits) {
    const words = ["00000","00001","00400","00401"];
    const groups=[];
    const count=Math.ceil(bits.length/2);
    for(let end=count;end>0;end-=8192){
      const start=Math.max(0,end-8192);
      const row=[];
      for(let i=end-1;i>=start;i--)row.push(words[bits[2*i]+2*(bits[2*i+1]||0)]);
      groups.push(row.join(""));
    }
    return BigInt("0x"+groups.join(""));
  }
  const squares=new Uint8Array(maximumRoot*maximumRoot+1);
  for(let k=1;k<=maximumRoot;k++)squares[k*k]=1;
  const digits=pack(sf)*pack(squares);
  const U=BigInt(high+1),L=BigInt(low);
  const unit=(1n<<(10n*U))-1n;
  const ones=unit/1023n;
  const guards=(ones-((1n<<(10n*L))-1n)/1023n)<<9n;
  const guarded=digits+411n*ones;
  const passed=(guarded&guards)===guards;
  const digit=n=>Number((digits>>BigInt(10*n))&1023n);
  return {low,high,maximumRoot,passed,atLowMinus1:digit(low-1),atLow:digit(low),atWorst:digit(5336100),atHigh:digit(high)};
}

const result = packedProduct(187426, 10252804, 503);
assert.equal(result.passed, true);
assert.equal(result.atLowMinus1, 97);
assert.equal(result.atLow, 288);
assert.equal(result.atWorst, 101);
assert.equal(result.atHigh, 164);
console.log(JSON.stringify(result, null, 2));

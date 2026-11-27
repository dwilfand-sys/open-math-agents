'use strict';

const fs = require('node:fs');
const {pairMultiplier} = require('./lagneau_linear_tail.cjs');
const limit = Number(process.argv[4]);
const path = process.argv[5];
if (!Number.isSafeInteger(limit) || limit < 100 || limit > 20000 || !path)
  throw Error('Expected medium prime cutoff and checkpoint file');
const lower = 14_000_000, upper = 1_000_000_000, block = 262144;
function prime(n) {
  for (let d=2; d*d<=n; ++d) if (n%d===0) return false;
  return n>1;
}
const old = fs.existsSync(path) ? fs.readFileSync(path,'utf8').trim().split('\n').filter(Boolean).map(JSON.parse) : [];
const bySlope = new Set(old.map(v=>v.slope));
for (const row of old)
  if (row.lower!==lower || row.upper!==upper || row.block!==block) throw Error('Incompatible checkpoint');
for (let slope=77; slope<=limit; slope+=6) {
  if (!prime(slope) || bySlope.has(slope)) continue;
  const v=pairMultiplier(lower,upper,slope,block);
  fs.appendFileSync(path,JSON.stringify({...v,block,factor:v.factor.toString()})+'\n');
}

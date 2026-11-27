'use strict';

const fs = require('node:fs');
const {build} = require('./lagneau_extra_residue_one.cjs');
const {ceilDiv, scale} = require('./lagneau_crt_bound.cjs');
const old = JSON.parse(fs.readFileSync(process.argv[4], 'utf8'));
const output = process.argv[5];
if (old.upper!==1_000_000_000 || old.smallLimit!==73 || old.maxDivisor!==20_000_000)
  throw Error('Unexpected previous table');
const upper = 10_000_000_000, block = 1_048_576;
const ext = build(old.maxDivisor,old.smallLimit,upper,block,old.upper);
const factors = old.factors.map((factors,j) => factors.map((v,k) =>
  ceilDiv(BigInt(v)*ext.factors[j][k],scale).toString()));
const counts = old.counts.map((counts,j) => counts.map((v,k) => v+ext.counts[j][k]));
const table = {...old, upper, factors, counts, nextLower: old.upper,
  nextBlock: block, extraFactors: ext.factors[0].map(String), extraCounts: ext.counts[0]};
fs.writeFileSync(output, JSON.stringify(table,null,2)+'\n');

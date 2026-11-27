'use strict';

const fs = require('node:fs');
const {pairMultiplier} = require('./lagneau_linear_tail.cjs');
const lower = 1_000_000_000;
// Arguments 2 and 3 select the base divisor and small prime cutoffs read
// by the shared sieve module. Their production values are 20000000 and 73.
const upper = Number(process.argv[4] || 10_000_000_000);
const path = process.argv[5];
const block = 1_048_576;
const slopes = [5, 11, 17, 23, 29, 41, 47, 53, 59, 71];
if (!path || !Number.isSafeInteger(upper) || upper <= lower) throw Error('Expected upper bound and checkpoint path');
const records = fs.existsSync(path) ? fs.readFileSync(path, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse) : [];
for (let i = 0; i < records.length; i++) {
  const row = records[i];
  if (row.slope !== slopes[i] || row.lower !== lower || row.upper !== upper || row.block !== block)
    throw Error('Saved range differs');
}
for (const slope of slopes.slice(records.length)) {
  const data = pairMultiplier(lower, upper, slope, block);
  fs.appendFileSync(path, JSON.stringify({...data, block, factor: data.factor.toString()}) + '\n');
  process.stdout.write(slope + ' ');
}

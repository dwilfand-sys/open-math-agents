'use strict';
const fs=require('node:fs');
const {bound}=require('./lagneau_large_singletons.cjs');
const rows=fs.readFileSync(process.argv[2],'utf8').trim().split('\n');
let total=0;
for(const line of rows) {
  const [lower,upper,count]=line.trim().split(/\s+/).map(Number);
  const actual=bound(lower,upper,1048576).total;
  if(actual!==count) throw Error('Mismatch in '+line);
  total+=actual;
}
console.log('Verified',rows.length,'bins and',total,'prime pairs.');

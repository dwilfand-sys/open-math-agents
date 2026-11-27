'use strict';
const fs=require('node:fs');
const {bound}=require('./lagneau_large_singletons.cjs');
const rows=fs.readFileSync(process.argv[2],'utf8').trim().split('\n');
const journal=process.argv[3];
const checked=journal && fs.existsSync(journal)?fs.readFileSync(journal,'utf8').trim().split('\n').filter(Boolean):[];
if(checked.length>rows.length || checked.some((r,i)=>r.trim()!==rows[i].trim()))throw Error('Journal mismatch');
let total=0;
for(const [i,line] of rows.entries()) {
  const [lower,upper,count]=line.trim().split(/\s+/).map(Number);
  if(i<checked.length){total+=count;continue;}
  const actual=bound(lower,upper,1048576).total;
  if(actual!==count) throw Error('Mismatch in '+line);
  if(journal)fs.appendFileSync(journal,line.trim()+'\n');
  total+=actual;
}
console.log('Verified',rows.length,'bins and',total,'prime pairs.');

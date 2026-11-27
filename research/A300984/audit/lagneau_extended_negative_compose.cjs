'use strict';
// node this.cjs 20000000 73 catalog-directory old-negative.json extra.jsonl
const fs = require('node:fs');
const path = require('node:path');
const base = require('./lagneau_crt_bound.cjs');
const {augment} = require('./lagneau_wide_graph.cjs');
const {positiveTailGraph} = require('./lagneau_extra_residue_one.cjs');
const {combine} = require('./lagneau_linear_tail.cjs');
const [, , , , catalog, negativeName, extraName, positiveName, starName, positiveStarName, layerName, positiveLayerName] = process.argv;
const read = name => JSON.parse(fs.readFileSync(name, 'utf8'));
const readCatalog = name => read(path.join(catalog, name));
if (base.maxDivisor !== 20_000_000 || base.smallLimit !== 73) throw Error('Incorrect baseline');
const edgeRows = readCatalog('CertifiedEdgesTriples.json');
const pairs = readCatalog('Double1B.json');
const positive = positiveName ? read(positiveName) : readCatalog('Positive1B.json');
const negative = read(negativeName);
const extra = extraName.split(',').flatMap(name=>
  fs.readFileSync(name, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse));
const single = augment(edgeRows);
const pairFilter = {
  makeGraph(factor, family, outer) {
    const masks = new Map();
    for (const row of pairs.rows) {
      const indices = row.selected.map(p => family.small.indexOf(p));
      if (indices.length !== 2 || indices.includes(-1)) throw Error('Unknown pair');
      masks.set((1 << indices[0]) | (1 << indices[1]), BigInt(row.survivalUpper));
    }
    return [masks, single.makeGraph(factor, family, outer)];
  },
  makeCorrection([masks, oldState], weights) {
    const original = single.makeCorrection(oldState, weights);
    return (weight, mask, seen) => {
      const old = original(weight, mask, seen);
      if (!masks.has(mask)) return old;
      const updated = base.ceilDiv(weight * masks.get(mask), base.scale);
      return updated < old ? updated : old;
    };
  },
};
const factors = new Map(negative.slopes.map(row => [row.s, BigInt(row.factor)]));
const extraSlopes = new Set();
const cutoffs = new Map(negative.slopes.map(row=>[row.s,negative.upper]));
for (const row of extra) {
  if (!factors.has(row.slope) || row.lower!==cutoffs.get(row.slope) ||
      !Number.isSafeInteger(row.upper) || row.upper<=row.lower)
    throw Error('Incompatible extension');
  extraSlopes.add(row.slope);
  cutoffs.set(row.slope,row.upper);
  factors.set(row.slope, base.ceilDiv(factors.get(row.slope) * BigInt(row.factor), base.scale));
}
function readStars(name,gated=false) {
  const bytes=fs.readFileSync(name);
  const content=name.endsWith('.gz')?require('node:zlib').gunzipSync(bytes):bytes;
  const lines=content.toString('utf8').trim().split('\n').filter(Boolean);
  if(name.endsWith('.jsonl'))return lines.map(JSON.parse);
  return lines.map(line=>{
    const [slope,small,count,factor]=line.trim().split(/\s+/);
    return {slope:Number(slope),small:Number(small),count:Number(count),factor,
      lower:gated?4_000_000:14_000_000,upper:gated?100_000_000:1_000_000_000};
  });
}
const rows = starName ? readStars(starName) : [];
const refined = rows.length ? require('./lagneau_star_correction.cjs').mediumStars(rows,pairFilter) : pairFilter;
const refinedBoth = positiveStarName
  ? require('./lagneau_star_correction.cjs').mediumStars(readStars(positiveStarName),refined,true) : refined;
const gatedNegative = layerName
  ? require('./lagneau_star_correction.cjs').mediumStars(readStars(layerName,true),refinedBoth,false,1000) : refinedBoth;
const gatedBoth = positiveLayerName
  ? require('./lagneau_star_correction.cjs').mediumStars(readStars(positiveLayerName,true),gatedNegative,true,1000) : gatedNegative;
const filtered = positiveTailGraph(positive, gatedBoth);
const result = combine(factors, base.maxDivisor, filtered);
const num = BigInt(result.numeratorUpper.replace('.', ''));
const afterOldSingletons = base.ceilDiv(num * 979789013592184n, base.scale);
const share = base.ceilDiv(afterOldSingletons * base.scale, 954333834230937n);
console.log(JSON.stringify({slopes: [...extraSlopes], preSingleton: num.toString(),
  afterOldSingletons: afterOldSingletons.toString(), beforePublishedCensus: share.toString()}));

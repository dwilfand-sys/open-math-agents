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
function readStars(name,gated=false,extension=false) {
  if(!name||name==='-')return [];
  if(name.includes(',')) return name.split(',').flatMap(path=>readStars(path,gated,extension));
  const parts=name.split('@');
  const multiplier=parts.length===2?Number(parts[0]):1;
  if(parts.length>2 || !Number.isSafeInteger(multiplier) || multiplier<1)throw Error('Bad center multiplier');
  name=parts.at(-1);
  const bytes=fs.readFileSync(name);
  const content=name.endsWith('.gz')?require('node:zlib').gunzipSync(bytes):bytes;
  const lines=content.toString('utf8').trim().split('\n').filter(Boolean);
  if(name.endsWith('.jsonl'))return lines.map(JSON.parse);
  return lines.map(line=>{
    const [slope,small,count,factor]=line.trim().split(/\s+/);
    return {slope:Number(slope),small:Number(small),count:Number(count),factor,multiplier,
      lower:gated?4_000_000:14_000_000,upper:gated||extension?100_000_000:1_000_000_000};
  });
}
const rows = starName ? readStars(starName) : [];
const {jointStars} = require('./lagneau_joint_star_bound.cjs');
const audit=process.argv[20]?require('./lagneau_record_prior.cjs').create(process.argv[20]):null;
const [mandatoryName,multiName,negExtended,positiveExtended]=process.argv.slice(12);
const quantile=process.argv[16]==='quantile'?require('./lagneau_joint_quantile.cjs').connect():undefined;
const readLong=name=>readStars(name).map(r=>({...r,lower:1_000_000_000,upper:3_000_000_000}));
const ranges=process.argv[19]?require('./lagneau_composite_ranges.cjs'):null;
const optional=ranges?ranges.open(process.argv[19]):{negative:{},positive:{},separate:[]};
const multiple=require('./lagneau_multiple_slopes_graph.cjs');
const mTable=mandatoryName && mandatoryName!=='-' ? multiple.read(mandatoryName,100_000_000,1_000_000_000) : null;
const mandatory=mTable?(mask,small)=>{
  const key=[5,11,17,23,29,41,47,53,59,71].reduce((sel,s,i)=>
    sel|((mask&(1<<small.indexOf(s)))?1<<i:0),0);
  return mTable[key];
}:undefined;
const neg = jointStars(rows,readStars(layerName,true),audit?audit.source(pairFilter):pairFilter,false,
  {rows:readStars(negExtended,false,true),longRows:readLong(process.argv[17]),
    mandatory:ranges?ranges.multiply(mandatory,optional.negative.long):mandatory,
    mandatoryShort:optional.negative.short,quantile});
const gatedBoth = jointStars(readStars(positiveStarName),readStars(positiveLayerName,true),neg,true,
  {rows:readStars(positiveExtended,false,true),longRows:readLong(process.argv[18]),
    mandatory:optional.positive.long,mandatoryShort:optional.positive.short,quantile});
const disjoint=multiName && multiName!=='-' ? multiple.extend(multiple.read(multiName,1_000_000_000,10_000_000_000),gatedBoth) : gatedBoth;
const withComposite=optional.separate.length?ranges.extend(optional.separate,disjoint):disjoint;
const filtered = positiveTailGraph(positive,audit?audit.result(withComposite):withComposite);
const result = combine(factors, base.maxDivisor, filtered);
const num = BigInt(result.numeratorUpper.replace('.', ''));
const afterOldSingletons = base.ceilDiv(num * 979789013592184n, base.scale);
const share = base.ceilDiv(afterOldSingletons * base.scale, 954333834230937n);
console.log(JSON.stringify({slopes: [...extraSlopes], preSingleton: num.toString(),
  afterOldSingletons: afterOldSingletons.toString(), beforePublishedCensus: share.toString()}));

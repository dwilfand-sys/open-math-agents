/* Two independent exhaustive finite checks for OEIS A085264.
 * Author: Codex for @dwilfand-sys, 2026-11-28.
 * Run with Node.js: node finite_503_roots.js
 *
 * The bit-plane checker sieves every square divisor; the scalar checker
 * sieves only squares of prime numbers. Both omit zero, since the remainder
 * must be a positive squarefree integer. Seven independent binary planes
 * suffice for counting up to 101: once a number reaches 101, it is removed
 * before another increment. Thus the first time the four bits of 101 are
 * all set is exactly its 101st witness, and no counter wraps.
 */
"use strict";

const assert = require("node:assert/strict");
const expectedFrequencies = [2,9,19,27,38,36,57,63,62,74,94,86,101,112,123,113,139,140,146,170,155,202,167,196,204,213,213,215,233,232,255,249,276,261,278,310,321,300,302,336,347,325,325,350,375,367,413,393,377,384,427,435,440,447,434,472,445,476,470,518,482,499,510,542,519,550,506,553,591,572,626,586,582,585,598,623,623,656,595,697,641,672,702,689,733,696,661,718,738,757,755,739,820,734,717,834,792,811,780,831,867];
const expectedLast = [13,61,85,196,225,441,621,909,1089,1125,1521,2025,2700,2200,2925,3969,3825,4500,5625,4869,6084,8100,11025,7425,9900,9981,10584,11925,12825,14400,13500,14625,18081,18225,17424,20925,22500,27225,21825,25425,27000,28224,27900,38025,44100,33300,35721,35325,39825,37044,39600,40725,44325,55125,50625,53100,52200,54000,60300,65025,63900,60025,63504,64125,74529,81225,77400,99225,88200,76500,79200,87525,90000,108900,88425,91800,95400,96300,100125,107325,132300];

function finiteTail(first, limit, maximumRoot) {
  const sf = new Uint8Array(limit + 1);
  sf.fill(1, 1);
  for (let d = 2; d * d <= limit; d++) {
    const q = d * d;
    for (let n = q; n <= limit; n += q) sf[n] = 0;
  }
  const words = Math.ceil((limit + 1) / 32);
  const flags = new Uint32Array(words);
  const alive = new Uint32Array(words);
  for (let n = 1; n <= limit; n++) {
    if (sf[n]) flags[n >>> 5] |= 1 << (n & 31);
    if (n >= first) alive[n >>> 5] |= 1 << (n & 31);
  }
  const planes = Array.from({length: 7}, () => new Uint32Array(words));
  const trace = [];
  let finalPositions = [];
  let k = 0;
  let remainingWords = words;
  for (k = 1; k <= maximumRoot && remainingWords; k++) {
    remainingWords = 0;
    let lastPositions = [];
    const shift = k * k, off = shift >>> 5, rem = shift & 31;
    for (let i = first >>> 5; i < words; i++) {
      let mask = alive[i];
      if (mask === 0) continue;
      const pos = i - off;
      let carry = pos >= 0 ? (flags[pos] << rem) : 0;
      if (rem && pos >= 1) carry |= flags[pos - 1] >>> (32 - rem);
      carry &= mask;
      for (let j = 0; j < 7 && carry; j++) {
        const old = planes[j][i];
        planes[j][i] = old ^ carry;
        carry &= old;
      }
      const finished = mask & planes[6][i] & planes[5][i] & planes[2][i] & planes[0][i];
      if (finished && lastPositions.length < 20) {
        for (let j = 0; j < 32 && lastPositions.length < 20; j++) {
          if ((finished >>> j) & 1) lastPositions.push(i * 32 + j);
        }
      }
      mask = (mask & ~finished) >>> 0;
      alive[i] = mask;
      if (mask) remainingWords++;
    }
    finalPositions = lastPositions;
    if (k % 50 === 0 || remainingWords === 0) {
      let remaining = 0;
      for (let w of alive) { while (w !== 0) { w = (w & (w - 1)) >>> 0; remaining++; } }
      trace.push([k, remaining]);
    }
  }
  return {first, limit, lastProcessed: k-1, remainingWords, finalPositions, trace};
}

function directCheck(first, limit, maximumRoot, lastInteger) {
  const primes = new Uint8Array(Math.floor(Math.sqrt(limit)) + 1).fill(1);
  primes[0] = primes[1] = 0;
  for (let p = 2; p*p < primes.length; p++) {
    if (!primes[p]) continue;
    for (let j = p*p; j < primes.length; j += p) primes[j] = 0;
  }

  const bad = new Uint8Array(limit + 1);
  bad[0] = 1;
  for (let p = 2; p < primes.length; p++) {
    if (!primes[p]) continue;
    for (let n = p*p; n <= limit; n += p*p) bad[n] = 1;
  }
  const squares = Array.from({length: maximumRoot + 1}, (_, k) => k*k);
  const histogram = new Uint32Array(maximumRoot + 1);
  let missed = 0;
  let hardest = [];
  let max = 0;
  for (let n = first; n <= limit; n++) {
    let hits = 0;
    let k = 1;
    for (; k <= maximumRoot && squares[k] < n; k++) {
      if (!bad[n-squares[k]] && ++hits === 101) break;
    }
    if (hits !== 101) {
      missed++;
      continue;
    }
    histogram[k]++;
    if (k > max) {
      max = k;
      hardest = [n];
    } else if (k === max) {
      hardest.push(n);
    }
  }
  const witnesses = [];
  for (let k = 1; k <= maximumRoot && k*k < lastInteger; k++) {
    if (!bad[lastInteger-k*k]) witnesses.push(k);
  }

  const frequencies = new Uint32Array(101);
  const last = new Uint32Array(101);
  for (let n = 1; n < first; n++) {
    let count = 0;
    for (let k = 1; k*k < n && count <= 100; k++) {
      if (!bad[n-k*k]) count++;
    }
    if (count <= 100) {
      frequencies[count]++;
      last[count] = n;
    }
  }
  return {
    first, limit, maximumRoot, missed, max, hardest, witnesses,
    tailRoots: Array.from(histogram).map((count, k) => [k, count])
      .filter(([k, count]) => k > 480 && count > 0),
    smallfreq: Array.from(frequencies), smalllast: Array.from(last)
  };
}

const low = 187426;
const high = 10252804;
const cap = 503;
const last = 5336100;
const packed = finiteTail(low, high, cap);
const direct = directCheck(low, high, cap, last);
assert.equal(packed.remainingWords, 0);
assert.equal(direct.missed, 0);
assert.equal(packed.lastProcessed, cap);
assert.equal(direct.max, cap);
assert.deepEqual(packed.finalPositions, [last]);
assert.deepEqual(direct.hardest, [last]);
assert.equal(direct.witnesses.length, 101);
assert.equal(direct.witnesses[99], 493);
assert.equal(direct.witnesses[100], cap);
assert.deepEqual(direct.smallfreq, expectedFrequencies);
assert.deepEqual(direct.smalllast.slice(0, expectedLast.length), expectedLast);
assert.equal(direct.smalllast[97], low-1);
assert.equal(Math.max(...direct.smalllast), low-1);
assert.equal(direct.smallfreq.reduce((a, b) => a + b, 0), 41931);
console.log(JSON.stringify({packed, direct}, null, 2));

'use strict';

// Run with Node.js 18 or later:
//   node workSquare/check_squarefree_counts_independent.cjs
// This scalar checker examines every 1 � n � 3202� = 10,252,804.
// It determines every frequency and last occurrence for 0,...,100 positive
// square-plus-positive-squarefree representations in that interval. Above
// 200,000 it expects every n to reach 101 representations; the latest 101st
// root on that range is 503, first attained at n = 5,336,100.
// The intermediate and unbounded mathematical estimates are separate.

const assert = require('node:assert/strict');

const maxCount = 100;
const prefix = 200_000;
const maxRoot = 3_202;
const limit = maxRoot * maxRoot;

function squarefreeFlags() {
  const flags = new Uint8Array(limit + 1);
  flags.fill(1, 1);
  // Include every possible square divisor, independently of any prime table.
  for (let d = 2; d <= maxRoot; ++d) {
    const square = d * d;
    for (let multiple = square; multiple <= limit; multiple += square) {
      flags[multiple] = 0;
    }
  }
  return flags;
}

function finiteCounts() {
  const squarefree = squarefreeFlags();
  const squares = Int32Array.from({ length: maxRoot + 1 }, (_, k) => k * k);
  const frequency = Array(maxCount + 1).fill(0);
  const last = Array(maxCount + 1).fill(-1);
  let largestExteriorRoot = 0;
  let firstLargestExteriorInput = 0;

  for (let n = 1; n <= limit; ++n) {
    let count = 0;
    let k = 1;
    // Reaching 101 excludes n from every class of interest. Otherwise the
    // loop exhausts all positive roots that leave a strictly positive summand.
    for (; k <= maxRoot && squares[k] < n && count <= maxCount; ++k) {
      count += squarefree[n - squares[k]];
    }
    if (count <= maxCount) {
      assert(n <= prefix, `Exterior input ${n} has only ${count} representations`);
      frequency[count]++;
      last[count] = n;
    } else if (n > prefix && k - 1 > largestExteriorRoot) {
      largestExteriorRoot = k - 1;
      firstLargestExteriorInput = n;
    }
  }
  return { frequency, last, largestExteriorRoot, firstLargestExteriorInput };
}

const result = finiteCounts();
assert.equal(result.largestExteriorRoot, 503);
assert.equal(result.firstLargestExteriorInput, 5_336_100);
assert.equal(Math.max(...result.last), 187_425);
assert.equal(result.frequency[100], 867);
assert.equal(result.last[100], 164_700);
console.log(JSON.stringify({ limit, prefix, ...result }));

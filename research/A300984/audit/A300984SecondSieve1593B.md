# A300984 prime-pair census through 1.593 trillion

Two implementations reproduced **27 consecutive new billion-wide counts** from 1,566,000,000,000 to 1,593,000,000,000, containing **44,093,916** pairs. It also reproduced nine additional bins beyond three gaps. Each row counts primes $r$ with $2r-1$ prime in an interval open on the left and closed on the right.

| Interval for $r$ in billions | Matched bins | Pairs |
|---|---:|---:|
| (1,566, 1,593] | 27 | 44,093,916 |
| (1,596, 1,599] | 3 | 4,894,796 |
| (1,602, 1,605] | 3 | 4,890,202 |
| (1,608, 1,611] | 3 | 4,893,719 |

The previous 566 matched bins in (1,000, 1,566] contained 938,684,595 pairs. The contiguous combined range now contains **982,778,511 pairs in 593 bins**. A certificate can also use the nine separate bins as written. Of the 1,000 primary bins from one to two trillion, 398 remain without a matching count in this checkpoint. The primary total over those 1,000 bins is 1,641,600,447.

The [primary table](CunninghamPrimary1566To2000B.txt) and [earlier verified bins](CunninghamPairedEndpointBins.txt) record the C# sieve's counts. The second implementation uses `lagneau_large_singletons.cjs`. Both programs sieve the same progressions $6k+1$ and $12k+1$. The C# program prefills a repeating wheel through 17. The JavaScript program starts with an unmarked block and strikes the two progressions for every trial prime from 5 upwards, beginning each form at the prime's square. The recorded agreement is on the aggregate count in each individual bin.

Run these commands from this directory to recompute every new row without reusing any prior verification journal.

```sh
node check_a300984_high_census.cjs CunninghamMinus1566BSecondSieveJournal.txt
node check_a300984_high_census.cjs CunninghamMinus1566BSecondSieveExtra.txt
```

The two new row files have LF-normalized SHA-256 digests `8e5031275474870a859b3352c2028bd166d2a35493ebf56149c6dbe5085d836e` and `14b214151daa43468e7b4d31d5eaa30ce4f1c06c3ab0ef455778763228ab62a8`, respectively. The two implementations compared the number of pairs in each bin.

These 36 disjoint bins supply 58,772,633 pairs. Starting from the archived 10,014,347,310,684,979 reciprocal-mass units, add the floor of $10^{18}n/U$ for each new bin containing $n$ pairs with upper endpoint $U$. The resulting lower bound is 10,051,406,990,214,168 units. The fifth-order exponential polynomial in the [finite counting criterion](A300984FiniteCountingCriterion.md) gives an upper bound of **0.501049006985** on the limiting proportion using only the corroborated low counts. It remains above one half.

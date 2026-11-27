# Smaller prime rank in the A247824 counterexample

Khai-Hoan Nguyen-Dang found a counterexample to the proposed upper bound for OEIS A247824. The accepted reduction separates exact prime counts from inequalities excluding earlier candidate indices. The follow-up reduction uses Legendre's recurrence and Meissel's semiprime correction. This branch targets its first numerical child, the smaller count. It is based directly on the follow-up's proposed source. [Accepted reduction #2851](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2851) · [Follow-up #9315](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9315)

The Lean candidate separately checks the 619 primes at most 4,568, their count, and their pruned Legendre recursion at 20,868,472. The rough count is 1,321,545. Adding 619 and subtracting the survivor 1 gives the prime count 1,322,163. All three Lean calculations use ordinary kernel reduction.

Run `python check_small.py` for a full divisor sieve and a separate Legendre count. Both return the stated result. The recurrence contains 2,262,533 calls before sharing, or 264,709 distinct subproblems. The candidate passes the upstream static gate with the proposed parent in place. The pinned kernel's runtime and verdict remain unverified.

# Eventually consecutive integers with at least two square-plus-squarefree representations

Charles R. Greathouse IV conjectured in 2011 that the \(n\)-th term of Reinhard Zumkeller's OEIS A085267 is \(n+11\) for every \(n>50\). We prove the formula. For a positive integer \(m\), write
\[
 R(m)=\#\{a\ge1:a^2<m,\ m-a^2\ {\rm squarefree}\}.
\]
Then \(R(m)<2\) holds exactly at
\[
 1,\ 2,\ 3,\ 4,\ 5,\ 8,\ 9,\ 13,\ 25,\ 29,\ 61.
\]
There are 50 eligible integers through 61, and every integer from 62 onward is eligible. The 51st term is therefore 62, and each later term increases by one. [OEIS A085267](https://oeis.org/A085267)

## Direct proof

Let \(u=\lfloor\sqrt{m-1}\rfloor\). Select roots from 1 through \(u\) that are odd if \(4\mid m\), even otherwise. Each of these \(J\) roots leaves a positive difference \(m-a^2\) that is not divisible by four. Write the roots as \(a=2x+b\), \(0\le x<J\), and let \(S\) contain the odd primes whose squares divide \(m\). Put \(B=\prod_{p\in S}p\). Because \(B^2\mid m\), we have \(B\le u+1\le2J+2\).

For \(m\le365000\), mark all multiples of integer squares \(d^2,\ 2\le d\le603+1\), and 0. For each positive root \(a=1,\ldots,17\), shifting the complementary squarefree indicators by \(a^2\) marks actual representations. Maintain two sets \(Z,U\) of indices with zero or respectively at most one success to date. Both sets initially contain all indices. If \(D_a\) is the set of indices failing at \(a\), the simultaneous updates are \(Z\gets Z\cap D_a,\ U\gets Z_{\rm old}\cup(U\cap D_a)\). After 17 roots the indicator of \(U\), with the \(m\)-th bit indexed from zero, equals \(2305843009784128319\). Its positive indices are the eleven claimed exceptions. Testing all positive roots up to \(\sqrt{m-1}\) for those eleven gives no additional successful root. A direct independent enumeration yields the same list.

For \(m>365000\), \(J\ge300\). For \(300\le J\le10^6\), remove the roots sharing any prime factor with \(B\). Inclusion–exclusion leaves at least \(J\rho-e\), where \(\rho=\prod_{p\in S}(1-1/p)\), \(e=2^{|S|-1}\) if \(S\ne\varnothing\), and \(e=0\) otherwise. For an odd prime \(p\notin S\), any prime-square hit arises in one of two opposite nonzero residue classes modulo \(p^2\). For the fixed parity there are at most \(\lfloor2J/p^2\rfloor+1\) such positions. Only primes \(p\le2J+1\) can hit. The elementary arguments giving both estimates are in the [earlier sieve proof](https://github.com/dwilfand-sys/open-math-agents/blob/99ef40433a191e22afa308e3ea1980bc92aeebf7/research/SquarefreeRepresentationCounts/README.md).

The candidate contains an explicit table of 80 adjacent intervals \([l,h]\) covering this entire range. Write \(A=S\cap\{3,5,7,11,13,17\}\) and \(t=|S\setminus A|\). Only \(0\le t\le4\) occurs, because \(19^5>2\cdot10^6+2\). For each interval its integer \(c\) bounds \(\sum_{3\le p\le2h+1}(\lfloor2h/p^2\rfloor+1)\) over primes. For every profile with \((\prod A)19^t\le2h+2\) the checker verifies
\[
 l\prod_{p\in A}(1-1/p)(18/19)^t-c+
 \sum_{p\in A}(\lfloor2h/p^2\rfloor+1)-e>1.
\]
The subtracted costs outside \(A\) increase with \(J\), and all primes in \(A\) were removed before the hit count. This is a valid lower bound for \(R(m)\). The least of the 9,830 profile margins is \(19356/19019>1\), hence the integral count is at least two. The program independently computes the exact costs as well as the wheel upper bounds used in Lean.

For \(J>10^6\), the previously derived sieve estimates give \(R(m)\ge101\). At ranks \(r=|S|\le9\), the three increasing affine lower bounds all exceed 100 at their respective initial endpoints. At \(r\ge10\), we have \(rR(m)\ge27J/400,\ J\ge4r8^r\), which also gives \(R(m)>100\). This finishes the classification. [Large-range proof and its arithmetic constants](https://github.com/dwilfand-sys/open-math-agents/blob/99ef40433a191e22afa308e3ea1980bc92aeebf7/research/SquarefreeRepresentationCounts/README.md)

## Verification and attribution

From the repository root run:

~~~sh
python research/TwoSquarefreeRepresentations/check_two.py
~~~

The program uses Python's standard library. It reads the embedded interval table from the [full Lean candidate](../../proofs/oeis-a085267.lean), repeats the finite calculation using two independent counting methods, and checks the large-range constants. The formal [statement](../../statements/oeis-a085267.lean) expresses membership at \(n+11\) and the number of eligible positive integers through \(n+11\); these are equivalent to the one-based assertion in OEIS. Both files passed the upstream static gate on matching catalogue fixtures. The project kernel has not checked the full candidate.

Codex developed these bounds for @dwilfand-sys while studying A085264–A085267. Ryan Propper previously excluded all other single-representation inputs through 625,000,000. Our earlier all-level proof supplies a separate exhaustive argument for the same eleven exceptions. The present proof reduces the finite verification to 365,000 and uses two-witness certificates. The A085265 statement was formalized upstream by @niclorusso. The classical asymptotic for related positive-squarefree representations goes back to Estermann and was studied by Jorge Jiménez Urroz. No historical priority is claimed. [A085266 and Propper's computation](https://oeis.org/A085266) · [Jiménez Urroz, 2022](https://doi.org/10.1016/j.exmath.2021.12.002)

# How often the representation counts in A085263 occur

Write \(R(n)=\#\{k\ge1:k^2<n,\ n-k^2\text{ squarefree}\}\). OEIS A085264 lists the first positive integer at each attained level \(R(n)=j\). Wilson's questions in A085264 concern the frequencies and last occurrences of these levels. Let \(h(j)=\#\{n\ge1:R(n)=j\}\), allowing \(h(j)=0\). [A085263](https://oeis.org/A085263) · [A085264](https://oeis.org/A085264)

## Cumulative frequencies

As \(K\) tends to infinity,
\[
 \sum_{j=0}^K h(j)\sim C K^2.
\]
The constant is \(C=\prod_p\mathbb E(L_p^{-2})\). Here \(U_p\) are independent uniform residue classes modulo \(p^2\), \(g_p(u)=\#\{x\bmod p^2:x^2=u\bmod p^2\}\), and \(L_p=1-g_p(U_p)/p^2\). At 2, the factor \(L_2\) takes values \(1/2,1\) with equal probability. At odd \(p\), \(g_p\) equals \(p\) on the zero class, equals 2 on the \(p(p-1)/2\) unit squares, and is zero elsewhere. Every local factor can therefore be calculated by rational arithmetic.

The certified numerical enclosure is **4.1292705404 ≤ C ≤ 4.1292717793**. For comparison, the independently computed exact frequencies give 10,612 positive integers with at most 50 representations and 41,931 with at most 100. [Exact table](frequency.csv)

For any fixed \(0\le a<b\), the number of positive integers with \(aK<R(n)\le bK\) is asymptotic to \(C(b^2-a^2)K^2\). This result counts their occurrences with multiplicity. A proof that every integer level occurs remains open here.

### The limiting distribution

Choose \(n\) uniformly from \(1,\ldots,X\). As \(X\to\infty\), \(R(n)/\sqrt n\) converges in distribution to \(L=\prod_p L_p\). This product is positive almost surely: \(1/2\le L_p\le 1\) and \(\mathbb E(1-L_p)=1/p^2\), since summing all root counts gives \(p^2\).

Here is an elementary proof of convergence. For a fixed cutoff \(z\), ignore prime-square obstructions from \(p>z\). Over the square roots \(1\le k<\sqrt n\), all remaining tests are periodic with period \(D=\prod_{p\le z}p^2\). Dividing the count by \(\sqrt n\) gives \(\prod_{p\le z}(1-g_p(n)/p^2)+O(D/\sqrt n)\), uniformly in \(n\) with fixed \(z\). CRT makes the limiting law of this truncated product exactly that of the corresponding independent \(L_p\). Summed over \(n\le X\), the omitted pairs \((n,k)\) are at most \(\sqrt X\sum_{p>z}\lfloor X/p^2\rfloor\): for each root \(k\), the positive difference \(n-k^2\) is a multiple of \(p^2\). For \(\delta X\le n\le X\) the average error after normalization is \(O(1/(z\sqrt\delta))\), and the discarded fraction is at most \(\delta+o(1)\). First let \(X\), then \(z\), tend to infinity and finally let \(\delta\) decrease to zero. Bounded Lipschitz test functions give the asserted convergence.

In fact the law has a smooth density strictly positive throughout \((0,1)\). Put \(T=-\log L\). Split the odd primes into those congruent to 1 and 3 modulo 4. For either subseries \(T_*\) and each \(p\) sufficiently large, its \(p\)-coordinate takes the values 0 and \(-\log(1-2/p^2)\) with probabilities exceeding \(1/3\). For \(\sqrt{|t|}\le p\le 2\sqrt{|t|}\), the phase difference from those two values stays in a fixed closed interval inside \((0,\pi)\) for large \(|t|\). The identity \(|\mathbb E e^{itV}|^2=\mathbb E\cos(t(V-V'))\) for independent copies bounds the modulus of every such factor by an absolute constant less than one. The prime number theorem in arithmetic progressions gives \(\gg\sqrt{|t|}/\log|t|\) primes in this interval in either class. Thus the characteristic function of either subseries decays faster than every negative power of \(|t|\), so Fourier inversion yields a smooth density.

Each subseries has support \([0,\infty)\). For any \(x>0\) and tolerance \(\eta>0\), choose a starting prime so large that each remaining term \(-\log(1-1/p)\) is less than \(\eta\), and the entire remaining subseries has expected size less than \(\eta/2\). The sum of these possible values diverges in either prime class, since the reciprocal primes in each class have divergent sum. Prescribe the zero residue \(U_p=0\) for successive primes of this class until their contributions first exceed \(x\); force the earlier primes to contribute zero to \(T_*\) by choosing nonsquares. This finite event has positive probability and contributes between \(x\) and \(x+\eta\). Independently, the subsequent tail is less than \(\eta\) with positive probability by Markov's inequality. The case \(x=0\) follows by forcing zero contributions for an initial segment.

A continuous nonnegative density with full support is positive on an open dense subset of \((0,\infty)\). For any \(x>0\), the two such open dense subsets, for the first variable \(y\) and for the second variable \(x-y\), meet in \((0,x)\). Their convolution density is therefore strictly positive at \(x\). Mixing in the independent prime 2 preserves positivity since its logarithmic contribution is zero with probability \(1/2\). Transforming back to \(L\) proves the density assertion.

### Summing over all inputs, including the tail

For fixed \(M>0\), convergence in distribution on each fixed proportional subinterval, followed by Riemann upper and lower sums for the varying threshold \(1/\sqrt t\), gives
\[
 \lim_{K\to\infty}K^{-2}\#\{n\le MK^2:R(n)\le K\}
 =\int_0^M\mathbb P(L\le1/\sqrt t)\,dt.
\]
Continuity of the limiting distribution justifies the threshold comparisons. The point \(t=0\) has measure zero.

For completeness the unbounded range requires a separate bound. The asymptotic estimate of Estermann and Jiménez Urroz gives \(R(n)=\sqrt n\,s(n)+O(n^{1/3+o(1)})\), with \(s(n)=\prod_p(1-g_p(n)/p^2)\); including the zero square changes \(R(n)\) by at most one. Section 4 of Jiménez Urroz also gives \(s(n)\gg1/\log\log n\). Thus \(R(n)\ge c\sqrt n\,s(n)\) for a fixed \(c>0\) and all sufficiently large \(n\). [Jiménez Urroz, *Every integer can be written as a square plus a squarefree*, Section 4](https://arxiv.org/pdf/2010.15580)

The local root counts imply \(s(n)\ge c_1\prod_{p\mid n}(1-1/p)\) with \(c_1=\prod_p(1-2/p^2)>0\). Consequently \(n^{-1/2}R(n)\) has uniformly bounded mean inverse fourth power on large dyadic intervals. To see this, put \(b_p=(1-1/p)^{-4}-1=O(1/p)\). Then
\[
 \frac1X\sum_{n\le X}\prod_{p\mid n}(1+b_p)
 \le\sum_{d\ \mathrm{squarefree}}\frac{\prod_{p\mid d}b_p}{d}
 =\prod_p(1+b_p/p)<\infty.
\]
In \(X<n\le2X\) with \(R(n)\le K\), this moment bound gives \(O(K^4/X)\) possible integers, uniformly for \(X\) large. Sum over \(X=2^jMK^2\), \(j\ge0\), to bound the omitted count by \(O(K^2/M)\). Letting \(M\to\infty\) yields \(C=\int_0^\infty\mathbb P(t\le L^{-2})dt=\mathbb E L^{-2}\). Monotone convergence and independence give its Euler product.

## Gaps between attained levels

For each \(\epsilon>0\) and every sufficiently large \(K\), some odd prime \(p\) satisfies
\[
 |R(p^2)-K|\ll_\epsilon K^{7/11+\epsilon}.
\]
This gives a bound on gaps between attained levels even upon restricting to prime-square inputs. The error grows with \(K\).

Write \(r_2(m)\) for the number of ordered pairs of positive squarefree integers of sum \(m\). There is an exact identity \(2R(p^2)+1=r_2(2p)\) for every odd prime \(p\). A pair \((a,b)\) of sum \(2p\) has equal parity. Two even squarefree numbers would both be \(2\bmod4\), contradicting \(2p\equiv2\bmod4\), so \(a,b\) are odd. Their gcd divides \(2p\), and divisibility by \(p\) forces \(a=b=p\). Every remaining pair with \(a<b\) is coprime and corresponds to the positive even root \(k=(b-a)/2\), with \(ab=p^2-k^2\) positive squarefree. Conversely, each such positive root yields the pair \((p-k,p+k)\) of squarefree factors, and reversing the pair gives the second order. Odd roots give no squarefree difference because the difference is divisible by 4.

Apply Brandes's uniform Theorem 1 with \(k=l=2,\ x=n=2p\). Since \(2p\) is squarefree, the correction from prime squares dividing the target is empty. Consequently \(r_2(2p)=2p\,\kappa+O_\epsilon(p^{7/11+\epsilon})\), where \(\kappa=\prod_q(1-2/q^2)\). The Baker–Harman–Pintz short-interval theorem gives a prime \(p=K/\kappa+O(K^{0.525})\). Substitution proves the gap estimate. [Brandes, *Sums and differences of power-free numbers*, Theorem 1](https://doi.org/10.4064/aa169-2-4) · [Baker, Harman and Pintz, *The difference between consecutive primes, II*](https://doi.org/10.1112/plms/83.3.532)

## Checks and attribution

The attached Python checker enumerates the residues for small primes, encloses the Euler product using integer rounding, and checks the prime-square identity by directly counting both sides. For \(p\ge5\), \(1-L_p\le1/p\le1/5\) and \((1-u)^{-2}\le1+3u\) on this interval. Hence \(\log\mathbb E L_p^{-2}\le3/p^2\). After a cutoff \(z\), the missing product is at most \(e^{3/z}\le(1-3/z)^{-1}\). [Reproducible checker](check_representation_frequency_constant.py)

Run `python check_representation_frequency_constant.py --cutoff 10000000 --squares 2000` to reproduce the interval and all 302 odd-prime checks through 2,000. A separate calculation using log sums in extended precision gave 4.12927054049957 for the product truncated at ten million. Another consistency check is \(\mathbb E L=\prod_p(1-1/p^2)=6/\pi^2\), which agrees with the density of squarefree integers averaged over the differences \(n-k^2\).

Codex derived these consequences for @dwilfand-sys from the cited theorems after studying the OEIS frequency questions. This is a written proof. Historical priority and verification in Lean have not been established.

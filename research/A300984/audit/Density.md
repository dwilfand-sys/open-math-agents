# Independent check of the A300984 density bound

Given a term bound \(Y\), count each odd prime dividing one or more terms once. This agrees with the published example, which lists distinct primes. Put \(X=\sqrt{Y}/2\). The calculations give an upper bound of **55.3131%** for the limit superior of the proportion of those primes in A082539. The conjecture of a strict majority at every power-of-ten cutoff remains open under this bound. [A300984](https://oeis.org/A300984) · [A082539](https://oeis.org/A082539)

## Eligible primes and the order of limits

Two distinct odd prime divisors of a term would make its sum of squarefree divisors, \(\prod_{\ell\mid n}(1+\ell)\), divisible by four. If at most one prime has exponent at least two, every nonsquarefree divisor is divisible by that prime squared, or the sum is zero. Consequently every term has form \(2^i p^j\) with \(i,j\ge2\). Its squarefree-divisor sum is \(3(p+1)\). Thus \(p\le X,\ p\equiv1\bmod12\) and \(p+1\) is squarefree. Write \(E(X)\) for the count of primes up to \(X\) with these properties.

For fixed \(R\), count reduced classes mod \(12\prod_{5\le r\le R}r^2\) by the prime number theorem in arithmetic progressions, where \(r\) ranges over primes. At \(r\) the admissible local class count is \(r(r-1)-1\). The ordinary relative prime density is

$$
\lim_{X\to\infty}E(X)/\pi(X)
=\tfrac14\prod_{r\ge5}\left(1-\frac{1}{r(r-1)}\right)>0.
$$

For this limit, the omitted \(p+1\) square divisors with \(R<r\le X^{1/4}\) cost \(O(\pi(X)/R)\) by Brun–Titchmarsh. For \(X^{1/4}<r\le\sqrt{X+1}\), summing \(X/r^2+1\) gives \(O(X^{3/4}+\sqrt X)\). Take \(X\to\infty\) first and \(R\to\infty\) second. The positive product allows division by \(E(X)\). In particular \(E(cX)/E(X)\to c\) for fixed \(c>0\). [Brun–Titchmarsh theorem and the prime number theorem in progressions](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/BrunTitchmarsh.pdf)

## Quadratic square-divisor tail

For \(A=7,15,31\), put \(B=A-3,\ F(x)=Ax^2+Bx+B,\ \Delta=B^2-4AB=-3(A-3)(A+1)\). Each discriminant is a fixed nonzero negative integer. Choose \(R>31\). For \(r>R\) there are at most two simple unit roots modulo \(r^2\). For \(R<r\le X^{1/4}\), Brun–Titchmarsh in each class gives \(O(X/(r(r-1)\log X))\), since \(r^2\le\sqrt X\). The normalized total is \(O(1/R)\). For \(X^{1/4}<r\le X^{2/3}\), counting all integers in the two classes costs \(O(X^{3/4}+X^{2/3})\).

For \(r>X^{2/3}\) set \(h=F(p)/r^2\). Then \(1\le h\ll_A X^{2/3}\). With \(u=2Ap+B,\ D=4Ah\), the equation is \(u^2-Dr^2=\Delta\). If \(D\) is a square, factoring gives \(O_\Delta(1)\) possibilities per \(h\). If \(D\) is nonsquare, sort solutions in each pair of residue classes of \(u,r\bmod|\Delta|\) by \(\alpha=u+r\sqrt D\). For two such solutions their ratio has coefficients \((u_2u_1-Dr_2r_1)/\Delta\) and \((r_2u_1-u_2r_1)/\Delta\), both integers, and norm one. If the ratio \(\epsilon\) exceeds one its rational coefficient is \((\epsilon+\epsilon^{-1})/2\), an integer at least two. Thus \(\epsilon\ge2+\sqrt3\). The bound \(1<\alpha=u+\sqrt{u^2-\Delta}\ll_A X+1\) proves \(O_\Delta(\log X)\) possibilities per \(h\), uniformly in \(D\). The total large-square cost is \(O_A(X^{2/3}\log X)=o(\pi(X))\).

These estimates let fixed-prime CRT products pass to the infinite squarefree conditions. The numerical tail \(1/19999\) follows by summing the limiting local probabilities after this passage.

## Local arithmetic and numerical bounds

For any eligible \(p\), \(p^2+p+1\equiv3\bmod9\). Thus \(F(p)\equiv3A-6\bmod9\), either 3 or 6, and each \(F(p)\) is odd. For \(r\ge5\) dividing \(B\), the only root mod \(r\) is the excluded zero class. This includes the repeated root for \(A=31,\ r=7\). If \(r\mid A\) there is one simple root whose lift equals \(-1\bmod r^2\) only if \(r^2\mid A\), which never occurs here. The ordinary discriminant test works at every other prime. The three root sets mod \(r^2\) are disjoint because two roots at offset \(t=1,2\) would force \(r^2\mid(2^t-1)(p+2)^2\), while \(F(-2)=3(A+1)\ne0\bmod r\).

Writing \(k=(p+1)/2\), any proper divisor \(d>1\) with \(2d-1\) prime excludes \(p\) from A082539. For a fixed finite obstruction list, \(d=k\) occurs for finitely many \(p\). The numerator script applies exact fixed-point multiplication with an upward round after each positive local factor. Integer products before conversion to BigInt are below \(2^{53}\). Independent runs of both programs reproduced all constants in the companion note.

For the outside shell \(X/\sqrt2<p\le X\), \(4p^2\) is the only possible term for sufficiently large \(X\). Let \(l=707106781186547/10^{15}\), \(u=l+10^{-15}\), \(c=1/19999\), and \(W_{\mathrm{lo}}=0.849112766182137\). The first witness alone succeeds with limiting proportion at least \(W_{\mathrm{lo}}\). In the two inner shells, respectively two and three witnesses are available. A union bound adds at most \(2c\) and \(3c\) to their finite-sieve joint failure probabilities. The overall failure therefore has limit superior at most

$$
(1-l)(1-W_{\mathrm{lo}})+(u-\tfrac12)(0.006980795097+2c)
+\tfrac12(0.000207592750+3c)<0.045839129432327 .
$$

The certified upper bound on the numerator, relative to \(E(X)\), is \(0.527775952949857\). Using the exact failure expression before decimal rounding gives the upper ratio

$$
\frac{10554991283044190143000000000000000}{19082263250482905356804459392486939}<0.553131 .
$$

## Finite samples

The rejection sampler draws from the candidates \(12t+1\) and filters for primes with squarefree \(p+1\). Under independent uniform draws this samples eligible primes uniformly with replacement. Fixed seeds make the computation reproducible. Statistical interpretation depends on the random-draw model and on choosing the cutoff, seed, sample size and analysis independently of the reported significance, or accounting for those choices.

If \(U\) bounds the sampled represented primitive count from above and \(L\) bounds the sampled represented nonprimitive count from below, the one-sided sign-test probability computed at \((U,L)\) is conservative under that model. Conditionally on the number represented, the true labels have a binomial law, and the lower tail increases with the count of primitive labels and decreases with the count of nonprimitive labels. An exact comparison uses \(\sum_{j=0}^{U}\binom{U+L}{j}/2^{U+L}\). Those probabilities concern the finite population with the chosen cutoff.

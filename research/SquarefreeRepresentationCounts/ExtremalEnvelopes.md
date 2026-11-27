# Sharp first- and last-occurrence envelopes for squarefree representations

Let \(R(n)\) count the positive integers \(a\) for which \(n-a^2\) is positive and squarefree. For integer \(k\ge1\) put
\[
 T(k)=\min\{n\ge1:R(n)\ge k\},\qquad
 L(k)=\max\{n\ge1:R(n)\le k\}.
\]
Then, with natural logarithms and Euler's constant \(\gamma\),
\[
 T(k)\sim k^2,\qquad L(k)\sim e^{2\gamma} k^2(\log\log k)^2.
\]
In OEIS A085264 the first and last tables concern **exactly** \(j\) representations. Thus \(L(k)\) is the largest last occurrence over the attained levels \(j\le k\), and \(T(k)\) is the smallest first occurrence over the attained levels \(j\ge k\). Existence of every individual level is a separate question. [A085263](https://oeis.org/A085263) · [A085264](https://oeis.org/A085264)

In fact \(T(k)-k^2=O(k^2/(\log k\log\log k))\). A second-moment estimate places an attained level between every sufficiently large \(k\) and \(k+O(k/((\log k)^{3/2}\sqrt{\log\log k}))\), with an absolute implied constant.

## A classical input and its uniform tail

Let \(g_p(n)\) count the roots of \(x^2=n\bmod p^2\). The asymptotic formula for unrestricted representations, in Section 4 of Jiménez Urroz, gives
\[
 R(n)=\sqrt n\,S(n)+O_\epsilon(n^{1/3+\epsilon}),\qquad
 S(n)=\prod_p(1-g_p(n)/p^2)
\]
for every \(\epsilon>0\). Excluding the square zero changes the count by at most one. The positive remainder convention affects at most another endpoint. We use the unrestricted count in that section, as distinct from the paper's separate primitive representation formula. Jiménez Urroz traces the asymptotic theory to Estermann. [Jiménez Urroz, *Every integer can be written as a square plus a squarefree*, Expositiones Mathematicae 40 (2022), 665–678](https://doi.org/10.1016/j.exmath.2021.12.002) · [Author's manuscript, Section 4](https://arxiv.org/pdf/2010.15580)

For odd \(p\), the root count is \(p\) when \(p^2\mid n\), two at a nonzero quadratic residue modulo \(p\), and zero otherwise. For \(p=2\) it is two for \(n=0,1\bmod4\), zero otherwise. Hence every local factor is at least \(1-1/p\). If \(y\ge3\), the loss in the product for \(p>y\) is at most
\[
 2\sum_{m>y}m^{-2}+\sum_{\substack{p>y\\p^2\mid n}}p^{-1}
 \ \ll\ 1/y+\frac{\log n}{y\log y}.
\]
Indeed the product of the squares in the latter sum divides \(n\), so there are at most \(\log n/(2\log y)\) such primes. We also used \(1-\prod(1-u_i)\le\sum u_i\).

Take \(y=\log n\). The large-prime product is \(1-o(1)\) uniformly. At the remaining primes Mertens' product theorem gives
\[
 \frac{R(n)}{\sqrt n}\ \ge\ \frac{e^{-\gamma}-o(1)}{\log\log n}.
\]
In particular \(R(n)\to\infty\), so each sublevel set defining \(L(k)\) is finite. [Mertens' product theorem](https://mathworld.wolfram.com/MertensTheorem.html)

## Both extremes in every polynomial-length interval

Fix \(0<\theta<1\) and \(I_X=[X,X+X^\theta]\). Write \(y=(\theta/8)\log X\). By the prime number theorem \(\sum_{p\le y}\log p\sim y\), so \(M=\prod_{p\le y}p^2<X^\theta/2\) eventually. Every class modulo \(M\) has a representative in \(I_X\). The loss bound above shows that all factors at primes above \(y\) have product \(1-o(1)\) uniformly for \(n\in I_X\).

* Taking \(n=0\bmod M\) makes the product up to \(y\) equal to \(\prod_{p\le y}(1-1/p)\sim e^{-\gamma}/\log y\). Together with the uniform lower bound and \(\log y\sim\log\log X\), this proves
  \[
    \min_{n\in I_X\cap\mathbb N}\frac{R(n)\log\log n}{\sqrt n}\longrightarrow e^{-\gamma}.
  \]
* At every odd prime up to \(y\), prescribe a nonresidue modulo \(p\). At 2 prescribe \(n=3\bmod4\). The Chinese remainder theorem gives \(n\in I_X\) and every prescribed local factor equals one. As \(R(n)\le\sqrt n\), this gives
  \[
    \max_{n\in I_X\cap\mathbb N}\frac{R(n)}{\sqrt n}\longrightarrow1.
  \]
* More generally, fix \(0<\alpha<1\). Keep the no-root conditions through \(y^\alpha\) and require \(p^2\mid n\) for \(y^\alpha<p\le y\). By Mertens, the product of the factors in this latter range tends to \(\log(y^\alpha)/\log y=\alpha\). The uniform tail and the representation formula give \(R(n)/\sqrt n=\alpha+o(1)\). The two extremal cases supply the endpoints. For every fixed \(\delta>0\), using a finite \(\delta/2\)-net of values of \(\alpha\) shows that the normalized counts in every such interval eventually come within \(\delta\) of every value in \([0,1]\).

## Passing to the inverse thresholds

The inequality \(R(n)\le\sqrt n\) gives \(T(k)\ge k^2\). For any fixed \(\eta>0\), apply the local maximum assertion with \(X=(1+\eta)k^2\) and \(\theta=1/2\). A point \(n\in I_X\) has \(R(n)\ge k\) for all sufficiently large \(k\). Thus \(\limsup T(k)/k^2\le1+\eta\), proving the first formula.

For the quantitative improvement, retain the no-root class modulo \(M\) in the proof of the local maximum. In fact \(M\le X^{\theta/2}\) for large \(X\), so it supplies \(N\gg X^{\theta/2}\) candidates in \(I_X\). For each \(p>y\), at most \(N/p^2+1\) of these satisfy \(p^2\mid n\), since they form a progression with step coprime to \(p\). Averaging the weighted loss from these primes gives
\[
 \frac{1}{N}\sum_n\sum_{\substack{p>y\\p^2\mid n}}\frac1p
 \le \sum_{p>y}p^{-3}+N^{-1}\sum_{p\le\sqrt{2X}}p^{-1}
 \ll y^{-2}+N^{-1}\log X.
\]
The unweighted local losses from the other large primes sum to at most \(2\sum_{p>y}p^{-2}\ll1/(y\log y)\), by summing the Chebyshev bound \(\pi(t)\ll t/\log t\) over dyadic ranges. Some candidate has weighted loss at most its average, giving \(R(n)/\sqrt n\ge1-O_\theta(1/(\log X\log\log X))\) after absorbing the representation-formula error. Take \(\theta=1/2\) and \(X=k^2(1+D/(\log k\log\log k))\) for a sufficiently large absolute \(D\). This candidate has \(R(n)\ge k\), while \(n-k^2=O(k^2/(\log k\log\log k))\). Finally \(R(T(k))\le\sqrt{T(k)}=k+O(k/(\log k\log\log k))\), giving the asserted gap bound for attained levels.

Put \(b(k)=e^{2\gamma}k^2(\log\log k)^2\). For fixed \(0<\eta<1\), take \(X=(1-\eta)b(k)\) in the local minimum assertion. Its minimizing \(n\) satisfies \(n/X\to1\), \(\log\log n/\log\log k\to1\), and \(R(n)/k\to\sqrt{1-\eta}<1\). This gives \(L(k)\ge(1-\eta)b(k)\) eventually. Conversely the function \(\sqrt x/\log\log x\) is increasing for all sufficiently large \(x\). Its value at \((1+\eta)b(k)\) is asymptotic to \(e^\gamma k\sqrt{1+\eta}\). The uniform lower bound now gives \(R(n)>k\) for every \(n\ge(1+\eta)b(k)\) when \(k\) is sufficiently large. Sending \(\eta\) to zero proves the second formula.

## Consequences for attained exact levels

We can locate an attained level more closely by centering at the mean remaining loss. Let \(y=(\log k)/16\), \(z=y^2\), \(\mu_y=\sum_{p>y}p^{-2}\) and \(\sigma_y=y^{-3/2}(\log y)^{-1/2}\). The previous no-root progression for \(p\le y\) has period \(M\le k^{1/4}\) for large \(k\). Uniformly for \(X\sim k^2\), its points in \([X,X+\sqrt X]\) form a progression of \(N\gg k^{3/4}\) candidates.

For \(y<p\le z\) write \(d_p(n)=g_p(n)/p^2\). In the uniform residue model modulo \(p^2\), the mean is \(p^{-2}\): count each pair \((n,x)\) with \(x^2=n\bmod p^2\) once by \(x\). The mean of \(g_p^2\) is \(1+2(p-1)/p<3\), from the squared root counts \(p^2\) at zero and 4 at each of the \(p(p-1)/2\) nonzero square classes. For two distinct primes the variables are independent in the residue model modulo their squared product.

These first and second moments transfer to the \(N\) candidates. For any function bounded by one of period \(Q\) coprime to \(M\), its progression average differs from its uniform residue average by at most \(2Q/N\), by splitting into full periods and a remainder. All periods needed for the centered sum \(\sum_{y<p\le z}(d_p-p^{-2})\) and its square are at most \(z^4\). Expanding the square has at most \(z^2\) ordered terms, each bounded by one. Hence the progression mean of its square is at most
\[
  3\sum_{p>y}p^{-4}+O(z^6/N)\ll \sigma_y^2 .
\]
The last estimate follows by dyadic summation of \(\pi(t)\ll t/\log t\). For \(p>z\) the mean of \(\sum d_p\) is \(O(1/z+\log X/N)=o(\sigma_y)\) by the preceding weighted loss bound and the ordinary tail. Chebyshev and Markov give a single candidate with \(\sum_{p>y} d_p=\mu_y+O(\sigma_y)\): take constants large enough that each of the two exceptional sets occupies less than half of the progression. Here \(\sum_{p>z}p^{-2}\ll1/z\).

For that candidate \(D=\sum_{p>y}d_p=O(1/(y\log y))\). The elementary bounds \(1-D\le\prod(1-d_p)\le e^{-D}\le1-D+D^2/2\) show \(S(n)=1-\mu_y+O(\sigma_y)\), since \(D^2=o(\sigma_y)\). Fix a sufficiently large absolute \(B\), and choose \(X\) by \(\sqrt X(1-\mu_y)=k(1+B\sigma_y)\). Our uniform bound, the change \(\sqrt n-\sqrt X=O(1)\), and the classical error \(O_\epsilon(n^{1/3+\epsilon})=o(k\sigma_y)\) for fixed \(\epsilon<1/6\), give
\[
 k\ \le\ R(n)\ \le\ k+O\!\left(\frac{k}{(\log k)^{3/2}\sqrt{\log\log k}}\right).
\]
This controls holes in the range of \(R\) without requiring \(T(k)\) to realize the sharper upper bound.

## Limiting constants for individual first and last occurrences

For an attained level \(j\), let \(a(j)\) and \(b_*(j)\) be its individual first and last occurrences. The local extremal sequences give the sharp statements
\[
 \liminf_{\substack{j\to\infty\\j\ \mathrm{attained}}}\frac{a(j)}{j^2}=1,\qquad
 \limsup_{\substack{j\to\infty\\j\ \mathrm{attained}}}
 \frac{b_*(j)}{j^2(\log\log j)^2}=e^{2\gamma}.
\]
For the first equality use \(a(j)\ge j^2\), then take \(j=R(n)\) along a local maximum sequence. For the second, \(b_*(j)\le L(j)\) is an upper bound. Take \(j=R(n)\) along a local minimum sequence. We have \(j\sim e^{-\gamma}\sqrt n/\log\log n\) and \(\log\log j\sim\log\log n\), while \(b_*(j)\ge n\). These deductions allow the two extremal sequences of levels to differ.

The Chinese-remainder constructions and inverse-envelope deductions above were developed by Codex for @dwilfand-sys from the published representation asymptotic and Mertens' theorem. A targeted literature search located no earlier statement of these precise OEIS envelope formulas. Historical priority is unconfirmed. This is a written mathematical proof.

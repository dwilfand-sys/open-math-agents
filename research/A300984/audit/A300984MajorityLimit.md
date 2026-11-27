# The limiting A082539 share among represented primes in A300984

Let \(N(Y)\) count the distinct odd primes represented in A300984 through \(Y\).
Let \(N_*(Y)\) count those among them for which no smaller prime \(q\) satisfies
\(q+1\mid p+1\). The fraction \(N_*(Y)/N(Y)\) has a limit as real \(Y\to\infty\),
and therefore along \(Y=10^m\). This follows from the signed shifted-prime
divisor estimate below and the previously established quadratic squarefree
sieve. These arguments give existence of the limit. Whether it is below
one half, and whether the strict majority holds at every exponent \(m>7\),
are separate questions. [A300984](https://oeis.org/A300984) · [A082539](https://oeis.org/A082539)

## A proper shifted-prime divisor of a shifted prime

There are absolute constants \(C,c>0\) such that for all real \(x\ge z\ge3\),
\[
 \#\{p\le x:p\text{ prime},\ \exists q\text{ prime},\
              z<q<p,\ q+1\mid p+1\}
 \ \le\ C\pi(x)(\log z)^{-c}.
\]
The proper-divisor condition matters. The choice \(q=p\) would include
every prime \(p>z\).

Luca, Pizarro-Madariaga and Pomerance proved the corresponding result
with \(q-1\) dividing \(up+v\), for fixed \(u>0,v\) and \(q\ne p\).
Their published Theorem 3 does not state the \(q+1\) case. The following
argument adapts their Section 3, identifying the changes to each of its
three estimates. We use their Lemma 4 itself with \(u=v=1\).
The required lower-tail estimate for the prime factors of \(q+1\)
also follows from Ford's uniform Hardy–Ramanujan inequality, Corollary 1
with shift \(+1\). [Luca, Pizarro-Madariaga and Pomerance, Theorem 3 and §3](https://math.dartmouth.edu/~carlp/irreg.pdf) · [Ford, Corollary 1](https://www.ford126.web.illinois.edu/wwwpapers/HR_shift.pdf)

Write \(p+1=a(q+1)\), so \(a\ge2\). Write \(\Omega\) for the number of
prime factors with multiplicity, and \(\Omega_q\) for the same count restricted
to primes at most \(q\). Put \(\alpha=2/3\) and \(H=x^{1/\log\log x}\) for
large \(x\). Bounds below allow a smaller positive exponent \(c\) to absorb
fixed powers of \(\log\log z\) or \(\log\log x\). Bounded \(x,z\) can be
included by increasing \(C\).

1. **Few factors in \(q+1\).** Suppose \(\Omega(q+1)\le\alpha\log\log q\).
   For \(z<q\le\sqrt{x}\), Brun–Titchmarsh bounds the number of corresponding
   \(p\) by \(O(\pi(x)\log\log q/q)\). The reduced class is
   \(-1\bmod q+1\). Ford's inequality bounds the number of such \(q\le t\)
   by \(O(\pi(t)/(\log t)^{c_0})\) for some \(c_0>0\). Indeed,
   \(\omega((q+1)/2)\le\Omega(q+1)\), and summing Ford's bound up to
   \(\alpha\log\log t\) gives any exponent strictly below
   \(1-\alpha+\alpha\log\alpha>0\) by Stirling's formula. Partial summation
   over \(q>z\) gives the required saving.

   For \(q>\sqrt{x}\), the smooth-number estimate used in the proof of
   Lemma 2 allows us to discard \(q+1\) whose prime factors are all at most
   \(H\). For clarity, when \(m>\sqrt{x}\) is such a value of \(q+1\), the
   number of multiples up to \(x+1\) is at most \((x+1)/m\). Dyadic summation
   and de Bruijn's smooth-number bound make the total \(O_A(x/(\log x)^A)\)
   for any fixed \(A\). Write \(q+1=br\) with a prime \(r>H\). At fixed
   \(a,b\) the three prime forms in \(r\) are
   \[
                r,\qquad br-1,\qquad abr-1 .
   \]
   Apart from primes dividing \(ab(a-1)\), the three roots modulo a prime
   are distinct. Here \(a-1\ne0\) is exactly where the proper-divisor
   condition is used. The three-dimensional upper-bound sieve in the
   proof of Lemma 2, equation (8), gives
   \(O(x(\log\log x)^5/(ab(\log x)^3))\). Signs of the constant terms
   only affect the exceptional-prime product just computed. In that bound
   one may use \(|ab(a-1)|/\varphi(|ab(a-1)|)\ll\log\log x\).
   The harmonic sum on \(a\) is \(O(\log x)\), and the restricted harmonic
   sum on \(b\), with \(\Omega(b)\le\alpha\log\log x\), is
   \(O((\log x)^{1-c_1})\), as in the end of Lemma 2. This gives the
   claimed saving for \(q>\sqrt{x}\). [Original three-form sieve and harmonic sum](https://math.dartmouth.edu/~carlp/irreg.pdf#page=7)

2. **Few small factors in \(a\).** Suppose
   \(\Omega_q(a)\le\alpha\log\log q\). We use the three ranges of Lemma 3.
   For \(q\le\exp(\sqrt{\log x})\), write \(a=a_1a_2\) with all prime
   factors of \(a_1\) at most \(q\) and all those of \(a_2\) greater than
   \(q\). Here \(a_1\le q^{\alpha\log\log q}<\sqrt{x}\) for all sufficiently
   large \(x\). At fixed \(a_1,q\) the
   remaining count for \(a_2\), rough to \(q\) with \(a_1(q+1)a_2-1\)
   prime, is
   \[
       \ll \frac{x}{\varphi(a_1(q+1))\log q\log x}
       \ll \frac{\pi(x)\log\log q}{a_1 q\log q}.
   \]
   For the second bound use \(\varphi(a_1(q+1))/(a_1(q+1))\gg
   1/\log\log q\): the primes dividing \(a_1(q+1)\) are at most \(q\),
   and \(\Omega(a_1)\le\alpha\log\log q\) gives
   \(\log\log(3a_1(q+1))\ll\log\log q\). The two sieve conditions remove
   the root zero for small prime factors of \(a_2\) and, at primes coprime
   to \(a_1(q+1)\), the root \((a_1(q+1))^{-1}\) for the prime form.
   The restricted harmonic sum of \(1/a_1\) is
   \(O((\log q)^{1-c_1})\). Summing over primes \(q>z\) gives the desired
   saving.

   For \(\exp(\sqrt{\log x})<q\le\sqrt{x}\), discard
   \(p\le x/(\log x)^3\). Then \(a\gg\sqrt{x}/(\log x)^3\).
   The smooth-number bound again permits discarding \(H\)-smooth \(a\),
   by summing \(O((x+1)/a)\) over these large smooth integers. Write
   \(a=a'r\) with \(r>H\) prime. The forms \(r,a'(q+1)r-1\) have distinct
   roots away from the primes dividing \(a'(q+1)\), giving the two-form
   upper bound \(O(x(\log\log x)^3/(a'(q+1)(\log x)^2))\) of Lemma 3.
   Its harmonic sum over \(a'\), with \(\Omega_q(a')\le\alpha\log\log q\),
   is \(O(\log x/(\log q)^{c_1})\). Summing \(1/(q(\log q)^{c_1})\)
   over primes \(q>z\) completes this range, after absorbing the
   \(\log\log x\) factors using \(\log q>\sqrt{\log x}\).
   For \(q>\sqrt{x}\), the three forms of part 1 apply again. Since
   \(a\le(x+1)/(q+1)<q\), \(\Omega(a)=\Omega_q(a)\); this time \(a\)
   has the restricted harmonic sum and \(b\) the unrestricted one. [Luca–Pizarro-Madariaga–Pomerance, Lemma 3](https://math.dartmouth.edu/~carlp/irreg.pdf#page=7)

3. **Too many small factors in the product.** In the remaining cases,
   every prime factor of the even integer \(q+1\) is at most \(q\), as
   \(q>3\). Hence
   \[
        \Omega_q(p+1)=\Omega(q+1)+\Omega_q(a)>
                  \tfrac43\log\log q .
   \]
   Lemma 4 of the cited paper bounds the number of \(p\le x\) for which
   this inequality holds for *some* \(q>z\) by
   \(O(\pi(x)/(\log z)^{c_2})\) with \(c_2>0\). Its statement allows
   any real cutoff \(w>z\) in place of \(q\) and directly applies to \(p+1\).
   The three cases prove the signed estimate. [Luca–Pizarro-Madariaga–Pomerance, Lemma 4](https://math.dartmouth.edu/~carlp/irreg.pdf#page=8)

## Combining the tail with squarefree conditions

Call a prime eligible if \(p\equiv1\bmod12\) and \(p+1\) is squarefree.
Let \(E(X)\) count eligible primes up to \(X\). Their density among all
primes is \(e=\frac14\prod_{\ell\ge5}(1-1/(\ell(\ell-1)))>0\), with
the product over primes. For \(i\ge2\), let
\(F_i(p)=2^{i+1}(p^2+p+1)-(p+2)^2\). For every fixed \(k\ge1\), let
\(B_k\) mean that at least one of \(F_2(p),\ldots,F_{k+1}(p)\) is
squarefree. Define \(g_k\) to be the limiting fraction among eligible
primes satisfying both \(B_k\) and the proper A082539 condition.

To prove that \(g_k\) exists, truncate the smaller primes \(q\) in the
proper-divisor condition to \(q\le z\). For \(p>z\) the condition is then
the finite set of exclusions \(p\not\equiv-1\bmod q+1\). The \(p\le z\)
contribute finitely many exceptions. Independently truncate all squarefree
tests, including eligibility, to prime squares \(\ell^2\) with \(\ell\le t\).
The resulting condition is periodic, possibly with shared moduli. Count its
allowed unit classes modulo their least common multiple and apply the prime
number theorem in arithmetic progressions. No independence between the
A082539 test and a squarefree test is needed.

For fixed \(k\), the linear and the fixed quadratic large-square estimates
show that the upper density of the primes whose squarefree tests change
tends to zero as \(t\to\infty\). The signed estimate bounds the upper
density lost by truncating \(q\) by \(C(\log z)^{-c}\). Thus, for any
\(\varepsilon>0\), the exact joint condition differs from a periodic
condition on upper prime density at most \(\varepsilon\). It follows that
its upper and lower prime densities coincide. Dividing by \(e>0\) proves
existence of \(g_k\). These statements use natural relative density among
primes, rather than logarithmic density. [Finite-pattern and square-divisor tail argument](A300984FinitePatterns.md)

Set \(X=\sqrt Y/2\) and \(w_k=2^{-(k-1)/2}\). The shape theorem gives
\(n=2^i p^j\) with \(i,j\ge2\). A term with \(j\ge3\) has
\(p\le X^{2/3}\), hence such terms can change the count of distinct primes by
only \(o(E(X))\). In the shell \(w_{k+1}X<p\le w_kX\), the available
exponents for \(j=2\) are exactly \(2,\ldots,k+1\). For an eligible prime
the witness \(2^i p^2\) is valid precisely when \(F_i(p)\) is squarefree.
Since \(E(tX)/E(X)\to t\) for each fixed \(t>0\), the \(k\)-th shell
contributes \((w_k-w_{k+1})g_k\) in the limit after division by \(E(X)\).
The combined contribution of all shells after \(K\) is between zero
and \(w_{K+1}\) in the limit superior. Consequently
\[
   \lim_{Y\to\infty}\frac{N_*(Y)}{E(\sqrt Y/2)}
       =G=\sum_{k\ge1}(w_k-w_{k+1})g_k,\qquad
   \lim_{Y\to\infty}\frac{N_*(Y)}{N(Y)}=\frac{G}{R},
\]
where \(R=\lim N(Y)/E(\sqrt Y/2)>0\) was bounded in the denominator
calculation. The constants in the signed tail bound have no explicit
numerical values in this note. Existence of \(G/R\) supplies neither its
value nor a finite cutoff with a certified error below the margin to
one half. [Represented-prime denominator and shell bounds](A300984RepresentedLimit.md)


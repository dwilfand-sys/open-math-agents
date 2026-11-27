# Arbitrarily large compulsory gcd in triangle representations

Let \(P(i,j)=(ij+i+j-\gcd(i,j))/2\) for integers \(i,j\ge2\). For every fixed \(B\ge2\), the number of positive integers \(n\le X\) with **no representation \(n=P(i,j)\) having \(\gcd(i,j)\le B\)** is
\[
 \gg_B X/(\log X)^{3/2}.
\]
This extends the restricted infinitude result of Petersen, Validashti and Wayland, who state that infinitely many integers are missing when the inputs must be coprime. A fixed bound on the gcd does not exhaust their possible representations. [Published article](https://doi.org/10.1080/0025570X.2026.2627861) · [OEIS A400795](https://oeis.org/A400795)

## A sieve estimate on a fixed progression

Let \(W\) be a fixed odd positive integer and \(l\) an integer with \(\gcd(l(4l+1),W)=1\). There are \(\gg_{W,l} Y/(\log Y)^{3/2}\) primes \(p\le Y\) congruent to \(l\bmod W^2\) for which every prime divisor of \(4p+1\) is \(1\bmod4\).

Here we use the sieve argument proving Lemma 14 of H. Iwaniec, *Primes represented by quadratic polynomials in two variables*, Acta Arithmetica 24 (1974), 435–459. The final theorem about representations by a quadratic form alone does not imply the required restriction at inert primes. The count denoted by \(\Sigma_3\) in its proof imposes that restriction directly. We give the specialization of the proof to identify the precise input. [Iwaniec, pp. 455–458, equations (45)–(59)](https://matwbn.icm.edu.pl/ksiazki/aa/aa24/aa2451.pdf)

Use the parameters \(A=4,\ B_{\rm Iw}=1,\ Cr^2d=1,\ \Delta=-4W^2,\ L_1=4l+1\bmod|\Delta|\). In this notation the modulus \(|T|\) preceding (50) is \(W^2\), and (50) says \(\gcd(L_1-1,4W^2)=4\). Conditions (47) and (48) have trivial gcds and (51) is vacuous. Equivalently, start the sieve at (52) with
\[
 \mathcal M=\{m=4p+1:p\le Y,\ p\ {\rm prime},\ p\equiv l\bmod W^2\}.
\]
Then \(m\equiv4l+1\bmod4W^2\), \(\gcd(m,2W)=1\), and the quadratic character for the field of discriminant \(-4\) is \(+1\) at \(m\). For every squarefree \(\lambda\) coprime to \(2W\), requiring \(\lambda\mid m\) gives exactly one reduced class of \(p\bmod \lambda W^2\). These are (52)–(55). The primes to be sieved out are exactly those \(q\equiv3\bmod4\) outside \(2W\); primes dividing \(W\) cannot divide \(m\).

For clarity, the signs and orders in the lower bound matter. For \(1<s<2\) near one, (57) gives a lower bound of size \(c_{W,l}\sqrt{s-1}\,Y/(\log Y)^{3/2}\) for avoiding the inert primes below \(Y^{1/(2s)}\), with a lower-order error. Its requisite progressions are the reduced classes just identified, to which the same Bombieri–Vinogradov estimate applies. An unremoved inert factor must be accompanied by another, counted with multiplicity, since \(m\equiv1\bmod4\). For fixed \(s<2\) and \(Y\) large, four such factors would exceed \(4Y+1\). The repeated-prime case contributes \(O(Y^{1-1/(2s)}+\sqrt Y)\) by counting multiples of squares. The switching estimate (58)–(59) bounds the remaining loss by \(C_{W,l}\sqrt{s-1}\log s\,Y/(\log Y)^{3/2}\). In (59) the fixed determinant factor is \(|AB_{\rm Iw}\Delta^2/(A,\Delta B_{\rm Iw})^2|=4W^4\), nonzero. The constants are independent of \(s\) sufficiently close to one. Taking \(s>1\) close enough to one proves the estimate. All parameters specifying the progression are fixed before \(Y\) tends to infinity.

## Excluding all bounded gcds

Let \(W\) be the product of all odd primes at most \(\max(3,B)\). Choose \(l\equiv1\bmod3\). At each \(s\mid W,\ s\ge5\), choose \(l\bmod s\) distinct from \(0,-1/4,1/2\). At most three residues are excluded. The Chinese remainder theorem now gives \(\gcd(l(4l+1)(2l-1),W)=1\). Use the primes in the preceding estimate and set \(n=2p-1\).

Suppose \(P(i,j)=n\) and write \(g=\gcd(i,j)\). We have \(g\mid2n\). Since \(n\) is odd and coprime to \(W\), every possible \(g\le B\) equals 1 or 2.

* For \(g=1\), \((i+1)(j+1)=2n+2=4p\). Since \(i+1,j+1\ge3\), the only factor pair is \(4,p\), up to order, once \(p>3\). It gives \(\gcd(i,j)=\gcd(3,p-1)=3\).
* For \(g=2\), write \(i=2a,\ j=2b\) with \(\gcd(a,b)=1\). Now \(n=2ab+a+b-1\). Because \(n\) is odd, \(a,b\) have the same parity and therefore are both odd. But \(4p+1=2n+3=(2a+1)(2b+1)\) would have a divisor \(3\bmod4\). This contradicts the prime factor condition.

The map \(p\mapsto n\) is injective. Applying the sieve estimate with \(Y=(X+1)/2\) gives the theorem.

## A sufficient estimate for full infinitude

For \(z\ge2\), the number of distinct \(n\le X\) having any representation with \(g>z\) is
\[
  \le\sum_{z<g\le\sqrt{2X}}\ \sum_{ab\le2X/g^2}1
  \ll X(1+\log X)/z .
\]
Indeed \(2P(ga,gb)=g^2ab+g(a+b-1)\ge g^2ab\). Thus a sufficient route to unrestricted infinitude would be to take \(z=(\log X)^4\) and find \(\gg X/((\log X)^{3/2}\log\log X)\) primes \(p\le(X+1)/2\) satisfying the earlier split-prime condition, \(p\equiv1\bmod3\), and such that \(2p-1\) has no odd prime factor at most \(z\). The displayed large-gcd count would be smaller than this lower bound.

The fixed-progression proof above supplies no uniform bound for that growing choice of \(W\). Nath and Xie use a vector sieve on different linear forms, \(p-1\) and \(p+2\). Their published theorem does not directly imply the sufficient estimate for \(4p+1\) and \(2p-1\). The growing-cutoff sieve remains to be justified. [Nath and Xie, Acta Arithmetica 223 (2026), 51–82](https://doi.org/10.4064/aa250227-19-11)

Codex developed this application for @dwilfand-sys. The counting estimate uses Iwaniec's sieve. This is a mathematical manuscript. It has no Lean verdict, and historical priority for the bounded-gcd statement is unconfirmed.

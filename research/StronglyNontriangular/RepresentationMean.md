# Mean number of generalized triangular representations

For the function of Petersen, Validashti and Wayland, let \(r(n)\) count unordered representations \(n=P(a,b)=(ab+a+b-\gcd(a,b))/2\) with \(2\le a\le b\). The sum of the representation counts has the two-term asymptotic
\[
 \sum_{n\le X}r(n)=X\log X+(\log 2+2\gamma-4)X+O(\sqrt X).
\]
Here \(\gamma\) is Euler's constant. Among representations counted up to \(X\), the limiting proportion with \(\gcd(a,b)=d\) is \(1/(\zeta(2)d^2)\) for every fixed positive integer \(d\). For example, \(6/\pi^2\) of the representations have coprime sides. Sampling weights each representation equally. The [prime-factor multiplicity note](Multiplicity.md) studies counts for uniformly sampled integers.

## Comparing with the divisor hyperbola

Take \(X\) integral and put \(M=2X+1\), \(A=a+1\), \(B=b+1\). The exact inequality \(P(a,b)\le X\) is \(AB\le M+\gcd(a,b)\). Thus every pair \(3\le A\le B\) with \(AB\le M\) qualifies. A qualifying pair outside this hyperbola satisfies
\[
 M/A<B\le M/A+(A-1)/A.
\]
For each \(A\) the interval contains at most one integer. Moreover \(2P(a,b)\ge ab\ge a^2\). The number of extra pairs is consequently at most \(\lfloor\sqrt{2X}\rfloor\).

Write \(D(M)=\sum_{j\le M}\lfloor M/j\rfloor\). Including all positive coordinates, the number of unordered pairs with \(AB\le M\) equals \((D(M)+\lfloor\sqrt M\rfloor)/2\). Removing \(A=1\) and \(A=2\) subtracts \(M+\lfloor M/2\rfloor-1\) for \(M\ge4\). With \(h=\lfloor\sqrt M\rfloor\), the exact identity \(D(M)=2\sum_{j\le h}\lfloor M/j\rfloor-h^2\) and the harmonic sum estimate give \(D(M)=M\log M+(2\gamma-1)M+O(\sqrt M)\). The first formula follows on substituting \(M=2X+1\).

## Distribution of the common divisor

Fix \(d\ge1\), put \(a=du,b=dv\), and count coprime \(u\le v\). Set \(Z=2X+d+1\), \(u_0=\lceil 2/d\rceil\) and \(U=\lfloor(\sqrt Z-1)/d\rfloor\). The conditions are exactly
\[
 u_0\le u\le U,\qquad u\le v\le \frac{Z/(du+1)-1}{d},\qquad \gcd(u,v)=1 .
\]
For each \(u\), inclusion-exclusion gives \(t\varphi(u)/u+O(\tau(u))\) integers \(1\le v\le t\) coprime to \(u\). Discarding \(v<u\) costs \(O(U^2)\) in all. Consequently the count is
\[
 \frac Z{d^2}\sum_{u_0\le u\le U}\frac{\varphi(u)/u}{u+1/d}+O_d(X).
\]
The identity \(\varphi(u)/u=\sum_{k\mid u}\mu(k)/k\) implies \(\sum_{u\le t}\varphi(u)/u=t/\zeta(2)+O(\log(2t))\). Partial summation now gives \((\log U)/\zeta(2)+O_d(1)\) for the displayed sum. Since \(Z=2X+O_d(1)\) and \(\log U=(\log X)/2+O_d(1)\), the fixed-\(d\) count is \(X\log X/(\zeta(2)d^2)+O_d(X)\). Dividing by the two-term asymptotic proves the proportion. These limiting proportions sum to one.

## Finite checks and attribution

Direct enumeration counted 936,298 unordered representations through 100,000, including 563,058 with coprime sides. Through 125,191 there are 1,200,253 representations, including 721,990 with coprime sides. The hyperbola omits respectively 14 and 12 pairs at those two endpoints. The unrestricted total through 125,191 also agrees with the previous [independent exhaustive check](README.md).

Codex derived these mean formulas for the project from the classical Dirichlet hyperbola method. Historical priority for this particular application and a Lean verdict are undetermined. The estimates concern multiplicity and supply no infinitude conclusion for the missing values. [Petersen, Validashti and Wayland](https://doi.org/10.1080/0025570X.2026.2627861) · [OEIS A400795](https://oeis.org/A400795)

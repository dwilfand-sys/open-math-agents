# Packing the remaining Cunningham pairs

The A401624 decade totals cited in the [finite census](A300984CunninghamCensus.md) give the number of primes $r$ in each remaining bin for which $2r-1$ is prime. A finite Selberg upper-bound sieve limits how closely those pairs can cluster at the top of the bin. This improves the lower bound on their reciprocal sum. The finite totals remain external inputs.

The primes exceed 3, so write $r=6k+1$ and $2r-1=12k+1$. For squarefree $d$ coprime to 6 put $g(d)=2^{\omega(d)}/d$ and $h(d)=\prod_{p\mid d}2/(p-2)$. Set $g(1)=h(1)=1$. For a finite level $z$ let

$$G=\sum_{d\le z}h(d),\qquad K=\sum_{d\le z}h(d)\prod_{p\mid d}(p+1),$$

where here and below the summed indices are squarefree and coprime to 6. For every closed interval of length $L$ in which $r$ and $2r-1$ exceed $z$, the number of Cunningham pairs is at most

$$\frac{L/6+1}{G}+\left(\frac K G\right)^2.$$

To see this, put $P(k)=(6k+1)(12k+1)$ and choose real weights $\lambda_d$ with support $d\le z$ and $\lambda_1=1$. The square of $\sum_{d\mid P(k)}\lambda_d$ majorizes the indicator that both linear forms are primes exceeding $z$. Over an interval of $N$ consecutive $k$, exactly $2^{\omega(j)}$ classes modulo $j$ give $j\mid P(k)$ by CRT. Their total count differs from $Ng(j)$ by at most $2^{\omega(j)}$. Thus the sum of the squares is at most

$$N\sum_{d,e}\lambda_d\lambda_e g([d,e])+\left(\sum_d 2^{\omega(d)}|\lambda_d|\right)^2.$$

Define $y_a=h(a)^{-1}\sum_{a\mid d}\lambda_d g(d)$. The identity $g([d,e])=g(d)g(e)\sum_{a\mid(d,e)}h(a)^{-1}$ makes the main quadratic form equal to $\sum_a h(a)y_a^2$. Take $y_a=\mu(a)/G$ and invert the finite multiple sums to obtain

$$\lambda_dg(d)=\frac{\mu(d)}G\sum_{d\mid a}h(a).$$

Then $\lambda_1=1$ and the main form is $1/G$. For the remainder,

$$\sum_d 2^{\omega(d)}|\lambda_d|=\frac1G\sum_a h(a)\sum_{d\mid a}\frac{2^{\omega(d)}}{g(d)}=\frac K G.$$

Finally $N\le L/6+1$, giving the asserted local bound. This derivation includes all errors and uses no asymptotic sieve estimate.

For $C$ pairs ordered downwards from their bin endpoint $U$, write $d_j=U-r_j$. The preceding bound applied to $[r_j,U]$ gives $d_j\ge6G(j-b)$ for $j>b$, where $b=1/G+(K/G)^2$. Lower-round $G$ and upper-round $K$ to retain a lower distance bound. For any consecutive group of ranks, the arithmetic sum of these lower bounds gives $D\le\sum_j d_j$. If the group has size $n$, Cauchy–Schwarz gives a reciprocal mass of at least $n^2/(nU-D)$. The code also divides the ranks into up to 128 groups and selects the strongest valid sieve level separately for each group. It takes the strongest result among these alternatives and the older wheel certificate and considers both the remaining count and the full decade. The earlier wheel bound applies within each explicitly enumerated small window.

The [integer implementation](lagneau_selberg_packing.py) uses a $10^{-20}$ fixed-point denominator for lower $h(d)$ and upper $h(d)\prod(p+1)$. Each operation on their sums, distances and reciprocal masses is rational. Run it with the numerator from the preceding composition, a comma-separated list of levels and the same consecutive window files. For example, 

```
python lagneau_selberg_packing.py 507178256670625 1000,3000,10000,20000,30000,50000,70000,100000,150000,200000,300000,500000,700000,1000000,1500000,2000000 CunninghamMinus10To100B.txt CunninghamMinus100To200B.txt CunninghamMinus200To1000B.txt
```

On the frozen example in that command, the reciprocal lower bound moves from $0.012907300091140$ to $0.013073838043080$ and the limiting ratio is at most $0.500590646789$. These numbers pertain to that numerator and those windows. More recent numerator bounds and additional census windows can be substituted directly.

The [small exact test](check_a300984_selberg_packing.py) verifies the quadratic-form identity by direct evaluation, checks 36 concrete prime-pair intervals and exercises the rank bounds. A [second coefficient calculation](check_a300984_selberg_coefficients.py) enumerates squarefree prime products recursively and constructs the exact rational summand before rounding. It independently confirms the safe directions for both coefficients at all 16 production levels through two million.

Codex developed this finite packing application for @dwilfand-sys in the analysis of Michel Lagneau's A300984. The quadratic optimization is Selberg's classical upper-bound sieve.

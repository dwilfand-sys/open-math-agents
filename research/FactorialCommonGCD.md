# The common divisor of the symmetric factorial ratios

For integers $m\ge1$ and $n,s\ge0$, set

$$
R_m(n,s)=\frac{(mn)!(ms)!}{n!s!((n+s)!)^{m-1}}.
$$

Consider the positive greatest common divisor of all the values with $n+s>0$. Then

$$
\gcd_{n+s>0} R_m(n,s)=G_m:=\frac{m\cdot m!}{\operatorname{lcm}(1,\ldots,m)}.
$$

The quotient $G_m$ is integral since each number through $m$ divides $m!$. Including $(0,0)$ would make the gcd 1, because $R_m(0,0)=1$. When $m=1$ all values are 1. Either input may vanish provided their sum is positive. The two-variable proof below gives an attaining pair with both inputs positive for each prime separately. It also gives the same common gcd if both inputs are required to be positive.

## Integrality and the contribution at a single prime power

Fix a prime $p$. For $j\ge1$ put $d=p^j$, $N=n+s$, $x=\{n/d\}$, $y=\{s/d\}$, where braces denote fractional part. Legendre's formula expresses the valuation of the rational ratio as the sum of the integers

$$
\Delta_j=\lfloor mx\rfloor+\lfloor my\rfloor-(m-1)\lfloor x+y\rfloor.
$$

All contributions eventually vanish. When $x+y<1$ the displayed expression is nonnegative. When $x+y\ge1$, the sum of the first two floors is at least $\lfloor m(x+y)\rfloor-1\ge m-1$. This proves integrality for every $m$ and is also a specialization of Chen and Wang's sufficient condition.

Multiplying both $n,s$ by $p$ preserves the valuation. The first contribution becomes zero and each later one shifts by a single position. We may therefore divide out all common powers of $p$ and assume $p$ does not divide at least one argument. This works unchanged when one argument is zero and the other is positive.

## Lower bound for every pair

Set $a=v_p(m)$, $b=v_p(N)$, and let $L$ satisfy $p^L\le m<p^{L+1}$. The claim is

$$
v_p(R_m(n,s))\ \ge\ v_p(m!)+a-L.
$$

For $1\le j\le b$, both arguments are nonzero modulo $p$ after the common scaling above. Their fractional parts modulo $p^j$ add to 1. When $j\le a$ as well, $mx$ and $my$ are integers, so $\Delta_j=1$. These indices give $\min(a,b)$.

For $j=b+t$, $1\le t\le L$, put $z=\{N/p^{b+t}\}$. Since $N/p^b$ is prime to $p$, $z\ge1/p^t$. The floor inequality gives

$$
\Delta_{b+t}\ge \lfloor mz\rfloor-1+\lfloor x+y\rfloor
                  \ge \lfloor m/p^t\rfloor-1.
$$

Whenever $j=b+t\le a$, both $mx$ and $my$ are integers, and the first inequality improves by 1. As $a\le L$, there are $\max(a-b,0)$ such indices. Adding the two bonuses gives $a$. Finally, the sum of $\lfloor m/p^t\rfloor$ over $1\le t\le L$ is $v_p(m!)$. All omitted terms are nonnegative. This proves the lower bound.

## A witness for each prime

Let $P=p^K$ with $K>a$ and $P>m(p+1)$. Set $t=p^L-1$, which lies between 0 and $m-1$. The interval $(tP/m,(t+1)P/m)$ has length greater than $p+1$ and contains an integer $n\equiv1\pmod p$. Its endpoints lie in $[0,P]$, so $n$ and $s=P-n$ are positive. Then

$$
\lfloor mn/P\rfloor=t,\qquad \lfloor ms/P\rfloor=m-1-t.
$$

For $1\le j\le K$, the fractional parts of $n/p^j$ and $s/p^j$ sum to 1. In this range $\Delta_j=1$ exactly when $p^j$ divides $mn$, and it is 0 otherwise. These terms contribute $a$. For $j=K+h$, $h\ge1$, the denominator factorials contribute zero. The remaining floors are $\lfloor t/p^h\rfloor$ and $\lfloor(m-1-t)/p^h\rfloor$. Thus

$$
v_p(R_m(n,s))=a+v_p\big((p^L-1)!\big)+v_p\big((m-p^L)!\big).
$$

For $1\le h\le L$, the difference of the three floors for $m$, $p^L-1$, and $m-p^L$ is 1. For $h>L$, all three are zero. Hence the last two factorial valuations add to $v_p(m!)-L$. This attains the lower bound at the specified prime. The construction applies also to $p>m$, when $L=a=0$.

Since $v_p(\operatorname{lcm}(1,\ldots,m))=L$, the lower bound gives divisibility by $G_m$ for every pair. Conversely, a common divisor has at each prime valuation at most that of the constructed witness, which is $v_p(G_m)$. This establishes the exact gcd without assuming that a single pair must work simultaneously for every prime.

## Relation to existing results

- The unnormalized integrality is an exact specialization of Xin Chen and Jane Wang's 2012 research manuscript. In §6.1.1, equation (10) and the condition before Remark 6.5, take two variables and $m+1$ linear forms: $n$, $s$, and $m-1$ copies of $n+s$. Each column sums to $m$ and $2m-(m+1)=m-1<m$. Landau's multivariable floor criterion gives a general earlier framework. [Chen and Wang, pp. 11–12](https://www-users.cse.umn.edu/~reiner/REU/ChenWang2012.pdf) · [Landau, 1900](https://www.numdam.org/item/NAM_1900_3_19__344_1/)
- For $m=2$, Gessel identifies $R_2/2$ with his super ballot numbers. Liu, Jiang and Yeh give the sharper identity $v_2(R_2(n,s))=s_2(n+s)$ in equation (3.1), where $s_p$ is the base-$p$ digit sum. [Gessel, §6](https://doi.org/10.1016/0747-7171(92)90034-2) · [Liu, Jiang and Yeh, equation (3.1)](https://ssmr.ro/bulletin/pdf/68-2/articol_7.pdf)
- When $m=p^e$, Legendre's digit-sum formula gives $v_p(R_m(n,s))=((m-1)/(p-1))s_p(n+s)$. Thus $p^{(m-1)/(p-1)}$ is the exact common *$p$-part*. Other primes may divide every term: $G_5=10$ and $G_8=384$. The arrays of Peter Bala are exactly $R_3(k,n+1)/3$ and $R_4(k,n+1)/8$. Here $G_3=3$ and $G_4=8$. [OEIS A361027](https://oeis.org/A361027) · [OEIS A361032](https://oeis.org/A361032)
- Farhi's row-lcm identity gives another expression, $G_m=m!/\operatorname{lcm}_{0\le j<m}\binom{m-1}{j}$. This identifies a known binomial factor in the answer. [Farhi, *American Mathematical Monthly*, 2009](https://arxiv.org/abs/0906.2295)

The statements above specify how the references apply. No priority claim is made for the exact common-gcd formula.

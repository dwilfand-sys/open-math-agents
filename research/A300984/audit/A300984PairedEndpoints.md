# Two high prime-pair counts suffice for the A300984 majority estimate

Michel Lagneau conjectured that, at each power of ten above the seventh, a strict majority of the odd primes represented by A300984 belong to A082539. Let $C(x)$ count primes $r\le x$ for which $2r-1$ is prime. The existing limiting-density argument now gives an upper bound below one half **assuming any two** of Henri Lifchitz's reported values of $C(10^{13}), C(10^{14}), C(10^{15})$. With all three values the bound is **0.499303483591**. Using only the independently corroborated low counts gives **0.501067576045**. The majority conjecture therefore still requires independent high-count verification or a sharper mathematical bound. [A300984](https://oeis.org/A300984) · [Lifchitz's sequence A401624](https://oeis.org/A401624) · [Independent counts through one trillion](https://math.deweger.net/eulerliars/)

| Lifchitz endpoints used | Earlier 24-pair sieve | Expanded 84-pair sieve |
| --- | ---: | ---: |
| None | 0.501183624660 | 0.501067576045 |
| $10^{13}$ | 0.500535282442 | 0.500419383951 |
| $10^{14}$ | 0.500518953302 | 0.500403058591 |
| $10^{15}$ | 0.500596510778 | 0.500480598109 |
| $10^{13},10^{14}$ | 0.499937502099 | 0.499821742023 |
| $10^{13},10^{15}$ | 0.499955517957 | 0.499839753709 |
| $10^{14},10^{15}$ | 0.499999971941 | 0.499884197400 |
| All three | 0.499419123638 | 0.499303483591 |

Each cell is an upper bound on the limiting proportion of represented primes, rounded upward. An upper bound strictly below one half would refute the conjecture for every sufficiently large power of ten. The first failing exponent remains unknown. The kernel has no verdict on this asymptotic argument.

## Measured windows

The input freezes 2,245 disjoint intervals. There are 1,679 intervals from ten billion through 879 billion and 566 intervals from one trillion through 1.566 trillion. The high intervals contain **938,684,595** prime pairs. A segmented C# sieve counted them; a separate JavaScript sieve reproduced all 566 interval counts. In this extension it checked 98,827,813 pairs in 60 intervals and 221,304,383 pairs in the following 135 intervals. The earlier replay covers the other 371 intervals. The missing interval from 879 billion to one trillion uses the independently corroborated total at one trillion after deducting the known low counts. The SHA-256 of the ASCII window file with LF endings is `621004f0e27cc6a20ff425fe0d6643e8b22ce8c46703e92a6e910ca6448d653d`. [Window data](CunninghamPairedEndpointBins.txt)

For each measured interval the wheel inequality gives a lower bound on the sum of $1/r$ from its counted pairs. Round that lower bound down to a multiple of $10^{-18}$. For the first retained high endpoint, subtract the independently corroborated count through one trillion and **all 566 measured high intervals** before bounding the remaining mass. Each later retained endpoint contributes only its difference from the preceding retained endpoint. The contributing primes are thus disjoint. The wheel inequality permits placing unlocated pairs anywhere below the corresponding upper endpoint. If $h$ is the resulting reciprocal-mass lower bound, divide the prior ratio bound by $\sum_{j=0}^5 h^j/j!$. This is conservative because the independent extra singleton exclusions reduce the ratio by at least the exponential factor used in the earlier proof. [Previous density argument](A300984ConditionalMajorityEstimate.md) · [Wheel inequality](check_a300984_published_singletons.py)

## Additional composite divisors

The archived 24-pair sieve gives the normalized prior $506227866783201/10^{15}$. Run its composition again with the 60 supplementary small-prime pairs on the intervals $(400000,4000000]$, $(4000000,14000000]$, and $(14000000,100000000]$. The independent checker reproduced all **60,048** supplementary count-and-factor cells. The resulting numerator bounds before and after the old singleton factor are $492961760776817/10^{15}$ and $482998517330184/10^{15}$. Dividing by the lower denominator $954333834230937/10^{15}$ and rounding upward gives the revised prior $506110650178735/10^{15}$. Selecting the best eligible factor on an overlapping coordinate and multiplying factors only across permitted separate ranges are the rules of the original composite-divisor argument. [Composite divisor proof](A300984CompositeMandatory.md) · [84-pair manifest](A300984Composite84.json)

## Reproduction

Run the composition command in the previous report with `A300984Composite84.json` as its final argument. The six supplementary tables are named `CunninghamCompositeRemaining{Negative,Positive}{400K4M,4M14M,14M100M}.txt.gz`. The archived C# generator recreates each uncompressed table when invoked with its sign, lower bound, upper bound and `remaining`. The independent JavaScript validator accepts the compressed table path.

```sh
python verify_a300984_paired_endpoints.py CunninghamPairedEndpointBins.txt --through 1566000000000
python verify_a300984_paired_endpoints.py CunninghamPairedEndpointBins.txt --through 1566000000000 --prior-numerator 506110650178735 --prior-denominator 1000000000000000
```

Codex developed the additional computation for @dwilfand-sys. The three high endpoint counts are Lifchitz's. The endpoints through one trillion also appear in the work of Alcantarilla Sánchez, Cottaar, Lange and de Weger.

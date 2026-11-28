# Three holes and cyclic semicircles: reconstructed proof

28 November 2026. Codex for @dwilfand-sys. This reconstructs the theorem
reported in the earlier private `Erdos142-semicircle-cover-threshold.md`;
the old proof file is unavailable in this container. No claim of publication
priority. Not yet refereed by Claude, and not Lean checked.

Attribution: the gap-doubling argument for odd moduli is prior mathematics.
The question and self-answer by user1673563, 7 August 2025, give the same
expanding-gap argument:
https://math.stackexchange.com/questions/5088408/does-iterated-angle-doubling-eventually-map-any-three-non-equally-spaced-points
That question prompted the reconstruction here. The parity reduction for
even moduli is written out below; its publication priority is unestablished.
The full result must not be advertised as a first discovery.

## Result

Let N be even and H a three-element subset of Z/NZ. Every progression

    {a, a+d, ..., a+(N/2-1)d},  gcd(d,N)=1,

meets H if and only if H contains an antipodal pair or is an equally spaced
triple. The second possibility requires 3|N. For odd N, hitting every
floor(N/2)-term unit-step progression is possible only for an equally spaced
triple (and that triple does hit all such progressions).

The formulation is about invertible steps on the cyclic group. It is not a
claim about arbitrary integer progressions or noninvertible cyclic steps.

## Gap formulation

For three distinct cyclic sites, let G be the largest cyclic distance between
successive sites. The longest run of sites avoiding H has G-1 points.
Consequently, hitting every k-term unit-step progression is equivalent to
G(uH)<=k for every unit u modulo N. Multiplication by d^{-1} explains the
equivalence with the progression formulation.

If there is no antipodal pair, G<=N/2 is the strict inequality G<N/2.
On the geometric circle this says the center lies strictly inside the
triangle. Call this the strict triangle condition.

## Two elementary geometric facts

1. If three positive circular gaps x,y,z sum to 1 and are all less than 1/2,
   their gaps after doubling the points are, in some order,
   1-2x, 1-2y, 1-2z. Thus the maximum absolute deviation from 1/3 doubles
   whenever the strict triangle condition continues to hold. A triple whose
   every doubling satisfies that condition must have x=y=z=1/3.

2. Replacing exactly one vertex of a strict triangle by its antipode puts
   the three vertices in an arc of length strictly less than 1/2. More
   precisely, the moved vertex lies strictly on the shorter arc between the
   other two vertices. To verify this, rotate the unchanged vertices to
   0 and b with 0<b<1/2. Their third vertex must lie in (1/2,b+1/2),
   and its antipode lies in (0,b).

Replacing two vertices is equivalent, up to rotating the whole triangle by
1/2, to replacing the remaining one.

## Proof for odd modulus

Doubling is a unit. Apply fact 1 repeatedly. If all unit multiples satisfy
the strict triangle condition, the initial triple is equally spaced.

## Removing powers of two

First suppose 4|N and the normalized triple {0,a,b} has mixed parity.
The unit u=1+N/2 fixes the even sites and moves the odd sites to their
antipodes. Fact 2 contradicts the strict triangle condition. Hence all
three sites have the same parity. Translate one to 0 and divide all sites
and the modulus by 2. Every unit of N/2 lifts to a unit of N, so the
condition descends. Repeat until the modulus is odd or twice an odd number.

It remains to treat N=2m with m odd. If the three sites have the same parity,
divide by 2 and apply the odd-modulus case. If they have mixed parity,
translate a majority-parity site to 0; the two majority sites are then even
and the remaining site c is odd. Move c by m to make it even too, obtaining
a triple Z on the subgroup of order m. There are still three distinct sites:
a coincidence would mean the original H had an antipodal pair.

The unit v=m+2 acts on even sites by doubling modulo 2m. It acts on the
adjusted odd site in exactly the same way: for odd c,

    v*c + m = 2*(c+m)  (mod 2m).

Thus v^j H, after the same adjustment of its minority site, equals 2^j Z.
By fact 2, for every j the distinguished adjusted site of 2^j Z would have
to lie strictly on the shorter arc between the other two.

That is impossible. Rotate one of those other sites to 0 and reflect if
needed. In principal coordinates the other is b and the distinguished site
is c, with 0<c<b<1/2. Double until b first crosses 1/2. Exact equality
cannot occur on the odd-order subgroup. At that step the principal value
of b becomes negative. Either c is still positive, or c is also negative
and has larger absolute value than b. In both cases c is no longer strictly
between 0 and b on their shorter arc. This contradiction settles mixed
parity and completes the necessity proof.

For sufficiency, every unit preserves an antipodal pair, whose gaps are at
most N/2. Every unit permutes an equally spaced triple, whose gaps are N/3.

## Three-hole threshold corollary

For a mask omitting exactly H, define tau(H)=max_{u unit} G(uH). This is the
smallest k for which the mask contains no cyclic k-term progression with
invertible step. An equally spaced triple has tau=N/3. An antipodal triple
has tau=N/2. Every other triple has tau>N/2. This classifies the masks with
three holes in the range k<=N/2, without asserting a classification above
that threshold.

## Verification and limits

### Uniform logarithmic set of test directions

The proof gives more than a triple-dependent multiplier. Write N=2^v*m,
where m is odd, and q=ceil(log2(m)), with q=0 for m=1. Include the units
1+N/2^s for 1<=s<v. Also include, for 0<=j<=q, the odd representative
of 2^j modulo m in [1,2m) if v>0; for v=0 use 2^j modulo m. For m=1,
the representative is 1. This is a set of at most ceil(log2(N))+1 units
depending only on N, not on H.

Testing the semicircle condition in these directions is equivalent to
testing it in every unit direction for three-point sets. Indeed, the first
family detects mixed parity at every possible stage of the power-of-two
reduction. The second is exactly the doubling orbit at odd modulus, and
the lifted-doubling orbit at twice odd modulus. In the odd case a nonzero
gap deviation has size at least 1/(3m); after q doublings it cannot stay
strictly below 1/3. In the twice-odd mixed case the nonzero shorter-arc
coordinate has magnitude at least 1/m, so its first crossing of 1/2 also
occurs by q. These are the stopping bounds in the preceding proof.

This gives an O(log N)-direction obstruction test for three holes, rather
than a scan of all phi(N) directions. It does not extend here to four or
more holes. The constructive Python checker separately audits this
uniform family as well as the triple-dependent algorithm.

### Audit results

- A separate exhaustive C++ checker tested every normalized triple {0,a,b}
  for every even modulus through 500, checking all units directly. It agreed
  on 10,385,375 triples and made 26,921,951 unit tests.
  For the 17,545 triples at even moduli through 60 it also enumerated the
  actual progression sets directly, independently checking the gap criterion
  and the N/2 versus N/2+1 boundary.
- An independently written Python routine implements the proof's
  constructive multiplier (doubling, parity flip, or lifted doubling),
  rather than searching all units. It passed all 551,300 normalized triples
  for all moduli through 150, plus 100,000 seeded random triples with moduli
  below 10^12 (seed 142).
- The mathematical proof above is the basis of the general claim. The
  computations are finite audits, not kernel certificates.

import Mathlib

namespace OMA.AlmostPerfectTwoOdd

/-- The correction obtained after clearing the two geometric denominators
excludes all exponent patterns at levels divisible by four. The variables
P and R are the full prime powers and their exponents are even. -/
private theorem two_factor_arithmetic {q p r P R : ℤ} (hq : 3 ≤ q)
    (hp : q+2 ≤ p) (hr : p < r) (level : 4 ∣ q+1)
    (hP : p^2 ≤ P) (hR : r^2 ≤ R)
    (pCase : P=p^2 ∨ p^4≤P) (rCase : R=r^2 ∨ r^4≤R)
    (identity : ((q+1)*(p+r-1)-p*r)*P*R + q + (p-1)*(r-1) = q*(p*P+r*R))
    (squareIdentity : P=p^2 → R=r^2 → q*(p^2+p+1)*(r^2+r+1)+1=(q+1)*p^2*r^2) : False := by
  let C := (q+1)*(p+r-1)-p*r
  change C*P*R+q+(p-1)*(r-1)=q*(p*P+r*R) at identity
  have pp : 0 < p := by omega
  have rp : 0 < r := by omega
  have ppos : 0 < P := (sq_pos_of_pos pp).trans_le hP
  have rpos : 0 < R := (sq_pos_of_pos rp).trans_le hR
  have hpp : p ≤ p^2 := by nlinarith only [mul_nonneg pp.le (show 0 ≤ p-1 by omega)]
  have hrr : r ≤ r^2 := by nlinarith only [mul_nonneg rp.le (show 0 ≤ r-1 by omega)]
  have pair : 0 ≤ (p-1)*(r-1) := mul_nonneg (by omega) (by omega)
  have Clower : 1 ≤ C := by
    by_contra! h
    have neg := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (show C ≤ 0 by omega) ppos.le) rpos.le
    have h1 := mul_le_mul_of_nonneg_left (show 1 ≤ P by omega) pp.le
    have h2 := mul_le_mul_of_nonneg_left (hrr.trans hR) rp.le
    have h3 := mul_nonneg (show 0 ≤ r-p by omega) (show 0 ≤ r-1 by omega)
    have h4 := mul_nonneg (show 0 ≤ q-1 by omega)
      (add_nonneg (mul_nonneg pp.le ppos.le) (mul_nonneg rp.le rpos.le))
    nlinarith only [neg, identity, h1, h2, h3, h4, hp, rp]
  have rbound : r < (q+1)^2 := by
    have h := mul_nonneg (show 0 ≤ p-(q+1)-1 by omega) (show 0 ≤ r-(q+1) by omega)
    dsimp [C] at Clower
    nlinarith only [h, Clower]
  have prange : p+r < p^2 := by
    have h := mul_nonneg (show 0 ≤ p-1-(q+1) by omega) (show 0 ≤ p-1+(q+1) by omega)
    nlinarith only [rbound, h, pp, hp, hq]
  have rbound' : r ≤ p^2 := by omega
  have p2R : p^2 ≤ R := by
    have h := mul_nonneg (show 0 ≤ r-p by omega) (show 0 ≤ r+p by omega)
    nlinarith only [h, hR]
  have strict : P*R < q*(p*P+r*R) := by
    have h := mul_nonneg (show 0 ≤ C-1 by omega) (mul_nonneg ppos.le rpos.le)
    nlinarith only [h, identity, pair, hq]
  have pFixed : P = p^2 := by
    rcases pCase with done | pLarge
    · exact done
    · exfalso
      have hpr : q*r*p ≤ p^4 := calc
        q*r*p ≤ p*(p^2)*p := mul_le_mul_of_nonneg_right
          (mul_le_mul (show q ≤ p by omega) rbound' rp.le pp.le) pp.le
        _ = _ := by ring
      have h1 := mul_nonneg (mul_nonneg (show 0 ≤ q by omega) ppos.le)
        (sub_nonneg.mpr p2R)
      have h2 := mul_nonneg rpos.le (sub_nonneg.mpr (hpr.trans pLarge))
      have h3 := mul_lt_mul_of_pos_right strict pp
      have h4 := mul_pos (show 0 < p-(q+1) by omega) (mul_pos ppos rpos)
      nlinarith only [h1, h2, h3, h4]
  subst P
  have rFixed : R = r^2 := by
    rcases rCase with done | rLarge
    · exact done
    · exfalso
      let d := q*p^3-q-(p-1)*(r-1)
      have hd : (C*p^2-q*r)*R = d := by dsimp [d]; nlinarith only [identity]
      have dp : 0 < d := by
        have h1 := mul_nonneg pp.le (sub_nonneg.mpr rbound')
        have h2 := mul_nonneg (show 0 ≤ q-2 by omega) (pow_nonneg pp.le 3)
        have h3 := mul_nonneg pp.le (show 0 ≤ p^2-1 by omega)
        dsimp [d]
        nlinarith only [h1, h2, h3, hp, rp]
      have du : d < R := by
        have h3 : p^3 ≤ r^3 := by gcongr <;> omega
        have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ q by omega)
        have h5 := mul_lt_mul_of_pos_right (show q < r by omega) (pow_pos rp 3)
        dsimp [d]
        nlinarith only [h4, h5, rLarge, pair, hq]
      have hc : 1 ≤ C*p^2-q*r := by
        by_contra! h
        have hx := mul_nonpos_of_nonpos_of_nonneg (show C*p^2-q*r ≤ 0 by omega) rpos.le
        omega
      have hx := mul_le_mul_of_nonneg_right hc rpos.le
      nlinarith only [hx, hd, du]
  subst R
  have Cup : C ≤ q := by
    have h1 := mul_nonneg pp.le (show 0 ≤ r^2-p^2 by nlinarith only [p2R])
    have h2 := mul_pos (show 0 < p^2-(p+r) by omega) (sq_pos_of_pos rp)
    have hsum : p^3+r^3 < p^2*r^2 := by nlinarith only [h1, h2]
    by_contra! h
    have h3 := mul_le_mul_of_nonneg_right (show q ≤ C by omega)
      (mul_nonneg (sq_nonneg p) (sq_nonneg r))
    have h4 := mul_lt_mul_of_pos_left hsum (show 0 < q by omega)
    nlinarith only [h3, h4, identity, pair, hq]
  let w := p+r-1
  let A := C*(q+2)+3*q
  have hsquare := squareIdentity rfl rfl
  have wide : 3*q < w := by
    by_contra! h
    have hsum : (p-(q+1))+(r-(q+1)) < 2*q := by dsimp [w] at h; omega
    have h1 := mul_pos (sub_pos.mpr hsum)
      (show 0 < 2*q+((p-(q+1))+(r-(q+1))) by omega)
    have h2 := sq_nonneg (r-p)
    dsimp [C] at Cup
    nlinarith only [Cup, h1, h2]
  have prodEq : w*(A-w) = C^2-3*q-1 := by
    dsimp [w, A, C]
    nlinarith only [hsquare]
  have zero : A = w := by
    rcases lt_trichotomy w A with h | h | h
    · have hgap := mul_nonneg (show 0 ≤ w-1 by omega) (show 0 ≤ A-w-1 by omega)
      have hC := mul_nonneg (show 0 ≤ C by omega) (show 0 ≤ q+2-C by omega)
      dsimp [A] at hgap
      dsimp [A] at prodEq
      nlinarith only [hgap, hC, prodEq, hq]
    · exact h.symm
    · have hgap := mul_nonneg (show 0 ≤ w by omega) (show 0 ≤ w-A-1 by omega)
      have hC := mul_nonneg (show 0 ≤ C-1 by omega) (show 0 ≤ C+1 by omega)
      nlinarith only [hgap, hC, prodEq, wide]
  have hsq : C^2 = 3*q+1 := by rw [zero] at prodEq; nlinarith only [prodEq]
  obtain ⟨k, hk⟩ := level
  have mod4 : C^2%4 = 2 := by omega
  rw [pow_two, Int.mul_emod] at mod4
  have cases : C%4=0 ∨ C%4=1 ∨ C%4=2 ∨ C%4=3 := by omega
  rcases cases with h | h | h | h <;> rw [h] at mod4 <;> norm_num at mod4

/-- At a level divisible by four, the almost-perfect equation admits no two
ordered odd prime-power bases larger than the level, for any positive even
exponents. The argument in fact works for arbitrary integer bases in the
same range. Shnoudi's two-factor identity supplies the decisive symmetric
quadratic. Divisibility of the level by four excludes its zero case. -/
theorem exclude_two_bases {q p r a b : ℕ} (hq : 3 ≤ q) (hp : q+2 ≤ p)
    (hr : p < r) (hf : 4 ∣ q+1) (ha : 0 < a) (hb : 0 < b) (hea : Even a) (heb : Even b) :
    1 + q*(∑ i ∈ Finset.range (a+1), p^i)*(∑ i ∈ Finset.range (b+1), r^i) ≠
      (q+1)*(p^a*r^b) := by
  intro hit
  obtain ⟨u, hu⟩ := hea
  obtain ⟨v, hv⟩ := heb
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  let X := ∑ i ∈ Finset.range (a+1), (p : ℤ)^i
  let Y := ∑ i ∈ Finset.range (b+1), (r : ℤ)^i
  let P := (p : ℤ)^a
  let R := (r : ℤ)^b
  have hMain : 1 + (q : ℤ)*X*Y = ((q : ℤ)+1)*(P*R) := by
    dsimp [X,Y,P,R]
    exact_mod_cast hit
  have hpx : X*((p : ℤ)-1) = p*P-1 := by
    dsimp [X, P]
    rw [geom_sum_mul, pow_succ, mul_comm]
  have hry : Y*((r : ℤ)-1) = r*R-1 := by
    dsimp [Y, R]
    rw [geom_sum_mul, pow_succ, mul_comm]
  have Pmin : (p : ℤ)^2 ≤ P := by
    dsimp [P]
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 0<p) ha2)
  have Rmin : (r : ℤ)^2 ≤ R := by
    dsimp [R]
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 0<r) hb2)
  have Pcase : P=(p : ℤ)^2 ∨ (p : ℤ)^4≤P := by
    by_cases h : a=2
    · exact Or.inl (by simp [P,h])
    · right
      dsimp [P]
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 0<p) (by omega : 4≤a))
  have Rcase : R=(r : ℤ)^2 ∨ (r : ℤ)^4≤R := by
    by_cases h : b=2
    · exact Or.inl (by simp [R,h])
    · right
      dsimp [R]
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 0<r) (by omega : 4≤b))
  apply two_factor_arithmetic (q := (q : ℤ)) (p := (p : ℤ)) (r := (r : ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hp) (by exact_mod_cast hr)
    (by exact_mod_cast hf) Pmin Rmin Pcase Rcase
  · have h1 := congrArg (fun z : ℤ => z*((p : ℤ)-1)*((r : ℤ)-1)) hMain
    have h2 := congrArg₂ (fun x y : ℤ => (q : ℤ)*x*y) hpx hry
    nlinarith only [h1,h2]
  · intro hP hR
    have pZ : 2 ≤ (p : ℤ) := by exact_mod_cast (by omega : 2 ≤ p)
    have rZ : 2 ≤ (r : ℤ) := by exact_mod_cast (by omega : 2 ≤ r)
    have hX : X = (p : ℤ)^2+p+1 := by
      apply mul_right_cancel₀ (by omega : (p : ℤ)-1 ≠ 0)
      rw [hpx,hP]
      ring
    have hY : Y = (r : ℤ)^2+r+1 := by
      apply mul_right_cancel₀ (by omega : (r : ℤ)-1 ≠ 0)
      rw [hry,hR]
      ring
    rw [hP,hR,hX,hY] at hMain
    nlinarith only [hMain]

private theorem even_exponent_of_odd_geometric {p a : ℕ} (hp : Odd p)
    (h : Odd (∑ i ∈ Finset.range (a+1), p^i)) : Even a := by
  have aux (t : ℕ) : (∑ i ∈ Finset.range t, p^i)%2 = t%2 := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hodd : p^t%2=1 := Nat.odd_iff.mp hp.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hodd]
      omega
  have hmod := Nat.odd_iff.mp h
  have hm := aux (a+1)
  exact ⟨a/2, by omega⟩

private theorem lower_base {q p r a b : ℕ} (hq : Odd q) (hp : Odd p)
    (ha : 0 < a) (hit : 1+q*(∑ i ∈ Finset.range (a+1), p^i)*(∑ i ∈ Finset.range (b+1), r^i) =
      (q+1)*(p^a*r^b)) : q+2 ≤ p := by
  cases a with
  | zero => omega
  | succ t =>
    have h1 : p^t ≤ ∑ i ∈ Finset.range (t+1), p^i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (p^i)) (Finset.mem_range.mpr (by omega))
    have low : p^t+p^(t+1) ≤ ∑ i ∈ Finset.range (t+1+1), p^i := by
      rw [Finset.sum_range_succ]
      exact Nat.add_le_add_right h1 _
    have h2 : r^b ≤ ∑ i ∈ Finset.range (b+1), r^i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (r^i)) (Finset.mem_range.mpr (by omega))
    have hl := Nat.mul_le_mul_left q (Nat.mul_le_mul low h2)
    have hlt : q < p := by
      by_contra! h
      have hm := Nat.mul_le_mul_right (p^t*r^b) h
      simp only [pow_succ p t] at hl hit
      nlinarith only [hl, hit, hm]
    obtain ⟨u, hu⟩ := hq
    obtain ⟨v, hv⟩ := hp
    omega

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- An even integer containing exactly two distinct odd primes cannot be
almost perfect, regardless of the exponents. -/
theorem exclude_even_two_odd_primes {k p r a b : ℕ} (hk : 0<k)
    (hp : p.Prime) (hr : r.Prime) (hop : Odd p) (hor : Odd r) (hlt : p<r)
    (ha : 0<a) (hb : 0<b) :
    1+σ 1 (2^k*(p^a*r^b)) ≠ 2*(2^k*(p^a*r^b)) := by
  intro hit
  let q := σ 1 (2^k)
  have hQ : q+1 = 2*2^k := by
    dsimp [q]
    rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (m := 2) (by decide), pow_succ]
    have := Nat.two_pow_pos k
    omega
  have hlevel : 4 ∣ q+1 := by
    cases k with
    | zero => omega
    | succ k =>
      refine ⟨2^k, ?_⟩
      rw [hQ,pow_succ]; ring
  have hQ3 : 3 ≤ q := by
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) (show 1 ≤ k by omega)
    norm_num at hpow
    omega
  have hQodd : Odd q := by
    have := Nat.two_pow_pos k
    exact ⟨2^k-1, by omega⟩
  have h2c : (2^k).Coprime (p^a*r^b) :=
    (hop.pow.mul hor.pow).coprime_two_left.pow_left k
  have hpc : (p^a).Coprime (r^b) :=
    (((Nat.coprime_primes hp hr).mpr (ne_of_lt hlt)).pow_left a).pow_right b
  have hodd : Odd (σ 1 (2^k*(p^a*r^b))) := ⟨2^k*(p^a*r^b)-1, by omega⟩
  rw [isMultiplicative_sigma.map_mul_of_coprime h2c,
    isMultiplicative_sigma.map_mul_of_coprime hpc,
    sigma_one_apply_prime_pow hp,sigma_one_apply_prime_pow hr] at hodd hit
  have heA := even_exponent_of_odd_geometric hop (Nat.odd_mul.mp (Nat.odd_mul.mp hodd).2).1
  have heB := even_exponent_of_odd_geometric hor (Nat.odd_mul.mp (Nat.odd_mul.mp hodd).2).2
  have base : 1+q*(∑ i ∈ range (a+1), p^i)*(∑ i ∈ range (b+1), r^i) =
      (q+1)*(p^a*r^b) := by
    rw [hQ]
    simpa only [q,Nat.mul_assoc] using hit
  exact exclude_two_bases hQ3 (lower_base hQodd hop ha base) hlt hlevel ha hb heA heB base

private theorem exclude_even_one_odd_prime {k p a : ℕ} (hp : p.Prime) (ho : Odd p)
    (ha : 0<a) : 1+σ 1 (2^k*p^a) ≠ 2*(2^k*p^a) := by
  intro hit
  let q := σ 1 (2^k)
  let g := ∑ i ∈ range a, p^i
  have hQ : q+1 = 2*2^k := by
    dsimp [q]
    rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (m:=2) (by decide), pow_succ]
    have := Nat.two_pow_pos k
    omega
  have h1 : p^0 ≤ g :=
    single_le_sum (fun i _ => Nat.zero_le (p^i)) (mem_range.mpr ha)
  have hg : 0<g := by simpa using h1
  have hsum : (∑ i ∈ range (a+1), p^i)=g*p+1 := by
    rw [sum_range_succ' (fun i => p^i) a]
    simp_rw [pow_succ]
    rw [← sum_mul, pow_zero]
  have hstep : g + p^a = g*p+1 := by simpa only [sum_range_succ,g] using hsum
  have hcop : (2^k).Coprime (p^a) := ho.pow.coprime_two_left.pow_left k
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hp,
    sum_range_succ] at hit
  change 1+q*(g+p^a)=2*(2^k*p^a) at hit
  have hm := congrArg (fun z : ℕ => z*p^a) hQ
  have heq : g * p = g * (q+1) := by nlinarith only [hit, hm, hstep]
  have hpe := Nat.eq_of_mul_eq_mul_left hg heq
  obtain ⟨t, ht⟩ := ho
  omega

/-- An even almost-perfect integer is either a power of two or its odd core
has at least three distinct prime divisors. -/
theorem odd_core_one_or_three {k u : ℕ} (hk : 0<k) (ho : Odd u)
    (hit : 1+σ 1 (2^k*u) = 2*(2^k*u)) : u=1 ∨ 3 ≤ u.primeFactors.card := by
  by_cases h1 : u=1
  · exact Or.inl h1
  right
  by_contra! hsmall
  have hu0 : u ≠ 0 := by rintro rfl; simp at ho
  have prim (p : ℕ) (h : p ∈ u.primeFactors) : p.Prime ∧ Odd p ∧ 0<u.factorization p := by
    have hp := Nat.prime_of_mem_primeFactors h
    have hd := Nat.dvd_of_mem_primeFactors h
    exact ⟨hp, hp.odd_of_ne_two (fun he => ho.not_two_dvd_nat (he ▸ hd)),
      hp.factorization_pos_of_dvd hu0 hd⟩
  have hpos : 0<u.primeFactors.card := by
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd h1
    exact card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp,hd,hu0⟩⟩
  have prod := Nat.prod_primeFactors_pow_factorization hu0
  by_cases hone : u.primeFactors.card=1
  · obtain ⟨p, hs⟩ := card_eq_one.mp hone
    have h := prim p (by simp [hs])
    rw [hs, prod_singleton] at prod
    exact exclude_even_one_odd_prime h.1 h.2.1 h.2.2 (by simpa only [← prod] using hit)
  · obtain ⟨p,r,hpr,hs⟩ := card_eq_two.mp (show u.primeFactors.card=2 by omega)
    have hP := prim p (by simp [hs])
    have hR := prim r (by simp [hs])
    rw [hs, prod_insert (by simpa using hpr), prod_singleton] at prod
    have hit' : 1+σ 1 (2^k*(p^u.factorization p*r^u.factorization r)) =
        2*(2^k*(p^u.factorization p*r^u.factorization r)) := by
      simpa only [← prod] using hit
    rcases lt_or_gt_of_ne hpr with h | h
    · exact exclude_even_two_odd_primes hk hP.1 hR.1 hP.2.1 hR.2.1 h hP.2.2 hR.2.2 hit'
    · exact exclude_even_two_odd_primes hk hR.1 hP.1 hR.2.1 hP.2.1 h hR.2.2 hP.2.2 (by
        simpa only [Nat.mul_comm (r^u.factorization r) (p^u.factorization p)] using hit')

end OMA.AlmostPerfectTwoOdd

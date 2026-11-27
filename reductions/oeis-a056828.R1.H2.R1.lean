import OMAReductions.R_oeis_a056828_R1

/-!
Square multiples of each of the six exceptional kernels in OEIS A056828.

Represent a split prime as p = a² + 3 b². If 3 does not divide b, the
six identities below turn norm multiplication in ℤ[√-3] into a sum of
powerful numbers. The remaining split primes are all of the form a²+27b².
Three further rotations treat p = 17 mod 24 and p = 29 or 101 mod 120.
These classes are disjoint from the first one.

The classical binary quadratic form appears, for example, in B. C. Berndt and
R. J. Evans, “Sums of Gauss, Jacobi, and Jacobsthal”, J. Number Theory 11
(1979), Theorem 3.4 and its corollary. The construction below only uses
elementary norm identities and a finite pigeonhole argument.
-/

namespace OMA.R_oeis_a056828_R1_H2_R1

open OMA.S_oeis_a056828

private def Rep (n : ℕ) : Prop :=
  ∃ x y z : ℕ, (x = 0 ∨ IsPowerful x) ∧ (y = 0 ∨ IsPowerful y) ∧
    (z = 0 ∨ IsPowerful z) ∧ x + y + z = n

private lemma square_times_cube (a b : ℕ) : a ^ 2 * b ^ 3 = 0 ∨ IsPowerful (a ^ 2 * b ^ 3) := by
  by_cases ha : a = 0
  · exact Or.inl (by simp [ha])
  by_cases hb : b = 0
  · exact Or.inl (by simp [hb])
  refine Or.inr ⟨Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero ha) _) (pow_pos (Nat.pos_of_ne_zero hb) _), ?_⟩
  intro q hq hd
  rcases hq.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hq.dvd_of_dvd_pow h) 2) _
  · have hb2 : q ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd (hq.dvd_of_dvd_pow h) 2
    exact dvd_mul_of_dvd_right (hb2.trans (pow_dvd_pow b (by decide : 2 ≤ 3))) _

private lemma seeds {m : ℕ} (hm : m ∈ ({7, 15, 23, 87, 111, 119} : Finset ℕ)) :
    ∃ c d : ℕ, ∃ x z : ℤ, (m : ℤ) = (c : ℤ) ^ 2 * (d : ℤ) ^ 3 + x ^ 2 + 3*z ^ 2 ∧
      (x : ZMod 3) ≠ 0 ∧ (z : ZMod 3) ≠ 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 2, 1, by decide, by decide, by decide⟩
  · exact ⟨1, 2, 2, 1, by decide, by decide, by decide⟩
  · exact ⟨4, 1, 2, 1, by decide, by decide, by decide⟩
  · exact ⟨1, 2, 2, 5, by decide, by decide, by decide⟩
  · exact ⟨1, 2, 10, 1, by decide, by decide, by decide⟩
  · exact ⟨4, 1, 10, 1, by decide, by decide, by decide⟩

private lemma orient (a b x z : ℤ)
    (ha : (a : ZMod 3) ≠ 0) (hb : (b : ZMod 3) ≠ 0)
    (hx : (x : ZMod 3) ≠ 0) (hz : (z : ZMod 3) ≠ 0) :
    ∃ t : ℤ, t ^ 2 = b ^ 2 ∧ (3 : ℤ) ∣ 2*a*t*x + (a^2 - 3*t^2)*z := by
  have cert : ∀ u v i j : ZMod 3, u ≠ 0 → v ≠ 0 → i ≠ 0 → j ≠ 0 →
      2*u*v*i + u^2*j = 0 ∨ 2*u*(-v)*i + u^2*j = 0 := by decide +kernel
  rcases cert a b x z ha hb hx hz with h | h
  · refine ⟨b, rfl, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_⟩
    push_cast
    simpa only [show (3 : ZMod 3) = 0 by decide, zero_mul, sub_zero] using h
  · refine ⟨-b, by ring, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_⟩
    push_cast
    simpa only [show (3 : ZMod 3) = 0 by decide, zero_mul, sub_zero] using h

private lemma rotated {m p : ℕ} (hm : m ∈ ({7, 15, 23, 87, 111, 119} : Finset ℕ))
    (a b : ℤ) (hn : (p : ℤ) = a ^ 2 + 3*b ^ 2)
    (ha : (a : ZMod 3) ≠ 0) (hb : (b : ZMod 3) ≠ 0) : Rep (p ^ 2 * m) := by
  obtain ⟨c, d, x, z, he, hx, hz⟩ := seeds hm
  obtain ⟨t, ht, w, hw⟩ := orient a b x z ha hb hx hz
  let s : ℤ := (a^2-3*t^2)*x-6*a*t*z
  refine ⟨(p*c)^2*d^3, s.natAbs^2, w.natAbs^2*3^3,
    square_times_cube (p*c) d, ?_, square_times_cube w.natAbs 3, ?_⟩
  · simpa using square_times_cube s.natAbs 1
  · have hnorm : s^2 + 3*(2*a*t*x + (a^2-3*t^2)*z)^2 =
        (a^2+3*t^2)^2 * (x^2+3*z^2) := by dsimp [s]; ring
    have hpt : (p : ℤ) = a^2+3*t^2 := by rwa [ht]
    rw [hw, ← hpt] at hnorm
    apply Int.ofNat.inj
    push_cast
    try simp only [Int.natCast_natAbs, sq_abs]
    rw [he]
    linear_combination hnorm

private lemma small_norm_multiple {p : ℕ} (hp : p.Prime) (d : ℕ) (hd : 0 < d)
    (t : ZMod p) (ht : t^2 = -(d : ZMod p)) :
    ∃ x y k : ℤ, 0 < k ∧ k < (d : ℤ)+1 ∧ x^2+(d : ℤ)*y^2=(p : ℤ)*k := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f (q : Fin (p.sqrt + 1) × Fin (p.sqrt + 1)) : ZMod p :=
    (q.1.val : ZMod p) + t * (q.2.val : ZMod p)
  have hcard : Fintype.card (ZMod p) <
      Fintype.card (Fin (p.sqrt + 1) × Fin (p.sqrt + 1)) := by
    simpa [pow_two] using Nat.lt_succ_sqrt' p
  obtain ⟨a, b, hab, hsame⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  let x : ℤ := (a.1.val : ℤ) - b.1.val
  let y : ℤ := (a.2.val : ℤ) - b.2.val
  have hxy : (x : ZMod p) + t * (y : ZMod p) = 0 := by
    dsimp [x, y]
    push_cast
    dsimp [f] at hsame
    linear_combination hsame
  have hnorm : (p : ℤ) ∣ x^2 + (d : ℤ)*y^2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    linear_combination ((x : ZMod p) - t * (y : ZMod p)) * hxy + (y : ZMod p)^2 * ht
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! hzero
    apply hab
    rcases hzero with ⟨hx, hy⟩
    apply Prod.ext
    · apply Fin.ext
      dsimp [x] at hx
      omega
    · apply Fin.ext
      dsimp [y] at hy
      omega
  have hdint : 0 < (d : ℤ) := by exact_mod_cast hd
  have hpositive : 0 < x^2+(d : ℤ)*y^2 := by
    rcases hnonzero with hx | hy
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (mul_nonneg hdint.le (sq_nonneg y))
    · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (mul_pos hdint (sq_pos_of_ne_zero hy))
  have hs : p.sqrt^2 < p := by
    refine lt_of_le_of_ne (Nat.sqrt_le' p) ?_
    intro he
    exact (Nat.prime_iff.mp hp).not_isSquare ⟨p.sqrt, by simpa [pow_two] using he.symm⟩
  have hs' : (p.sqrt : ℤ)^2 < (p : ℤ) := by exact_mod_cast hs
  have hbnd (i j : Fin (p.sqrt + 1)) : ((i.val : ℤ) - j.val)^2 ≤ (p.sqrt : ℤ)^2 := by
    have hi := i.isLt
    have hj := j.isLt
    have hl : 0 ≤ (p.sqrt : ℤ) + ((i.val : ℤ) - j.val) := by omega
    have hr : 0 ≤ (p.sqrt : ℤ) - ((i.val : ℤ) - j.val) := by omega
    nlinarith only [mul_nonneg hl hr]
  have hupper : x^2+(d : ℤ)*y^2 < ((d : ℤ)+1)*(p : ℤ) := by
    have hx : x^2 ≤ (p.sqrt : ℤ)^2 := hbnd a.1 b.1
    have hy : y^2 ≤ (p.sqrt : ℤ)^2 := hbnd a.2 b.2
    calc
      _ ≤ (p.sqrt : ℤ)^2 + (d : ℤ)*(p.sqrt : ℤ)^2 :=
        add_le_add hx (mul_le_mul_of_nonneg_left hy hdint.le)
      _ = ((d : ℤ)+1)*(p.sqrt : ℤ)^2 := by ring
      _ < _ := mul_lt_mul_of_pos_left hs' (by positivity)
  obtain ⟨k, he⟩ := hnorm
  have hpint : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  refine ⟨x, y, k, ?_, ?_, he⟩
  · by_contra! hk
    exact (mul_nonpos_of_nonneg_of_nonpos hpint.le hk).not_gt (he ▸ hpositive)
  · by_contra! hk
    have hpk := mul_nonneg hpint.le (sub_nonneg.mpr hk)
    nlinarith only [hpk, he, hupper]

private lemma split_prime_norm {p : ℕ} (hp : p.Prime) (hbig : 31 < p)
    (hmod : p % 3 = 1) : ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 3 * b ^ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hd
  let v : ZMod p := u
  have hvo : orderOf v = 3 := orderOf_units.trans hu
  have hv3 : v ^ 3 = 1 := by simpa only [hvo] using pow_orderOf_eq_one v
  have hv1 : v ≠ 1 := by
    intro h
    simpa [h] using hvo
  have hfactor : (v - 1) * (v ^ 2 + v + 1) = 0 := by linear_combination hv3
  have hpoly := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hv1)
  let t : ZMod p := 2 * v + 1
  have ht : t ^ 2 = -3 := by
    dsimp [t]
    linear_combination 4 * hpoly
  obtain ⟨x, y, k, hkpos, hklt, he⟩ := small_norm_multiple hp 3 (by decide) t ht
  norm_num at hklt he
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact ⟨x, y, by simpa using he.symm⟩
  · have hodd := hp.eq_two_or_odd.resolve_left (by omega)
    have hhalf : (p : ℤ) = 2 * ((p / 2 : ℕ) : ℤ) + 1 := by omega
    rw [hhalf] at he
    have h4 := congrArg (fun n : ℤ => (n : ZMod 4)) he
    push_cast at h4
    have cert : ∀ i j c : ZMod 4, i ^ 2 + 3 * j ^ 2 ≠ (2 * c + 1) * 2 := by decide
    exact False.elim (cert _ _ _ h4)
  · have h3 := congrArg (fun n : ℤ => (n : ZMod 3)) he
    push_cast at h3
    have cert : ∀ i j c : ZMod 3, i ^ 2 + 3 * j ^ 2 = c * 3 → i = 0 := by decide
    obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp (cert _ _ _ h3)
    refine ⟨y, z, ?_⟩
    rw [hz] at he
    nlinarith only [he]

private lemma pr17_norm_two {p : ℕ} (hp : p.Prime) (t : ZMod p) (ht : t ^ 2 = -2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 2 * b ^ 2 := by
  obtain ⟨x, y, k, hkpos, hklt, he⟩ := small_norm_multiple hp 2 (by decide) t ht
  norm_num at hklt he
  have hcases : k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl
  · exact ⟨x, y, by simpa using he.symm⟩
  · have h2 := congrArg (fun n : ℤ => (n : ZMod 2)) he
    push_cast at h2
    have cert : ∀ i j c : ZMod 2, i ^ 2 + 2 * j ^ 2 = c * 2 → i = 0 := by decide
    obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp (cert _ _ _ h2)
    refine ⟨y, z, ?_⟩
    rw [hz] at he
    nlinarith only [he]

private lemma pr17_even {x : ℤ} (h : 4 * (x : ZMod 8) = 0) : (2 : ℤ) ∣ x := by
  have hx : ((4 * x : ℤ) : ZMod 8) = 0 := by push_cast; exact h
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * x) 8).mp hx
  omega

private lemma prime_four {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ a c : ℤ, (p : ℤ) = a^2+4*c^2 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have he : (a : ℤ)^2+(b : ℤ)^2=p := by exact_mod_cast hab
  have hp4i : (p : ℤ) = 4*((p/4 : ℕ) : ℤ)+1 := by omega
  have hc := congrArg (fun n : ℤ => (n : ZMod 8)) (he.trans hp4i)
  push_cast at hc
  have cert : ∀ i j k : ZMod 8, i^2+j^2=4*k+1 → 4*i=0 ∨ 4*j=0 := by decide +kernel
  rcases cert _ _ _ hc with ha | hb
  · obtain ⟨c, h⟩ := pr17_even (x := (a : ℤ)) (by exact_mod_cast ha)
    exact ⟨b, c, by rw [h] at he; nlinarith only [he]⟩
  · obtain ⟨c, h⟩ := pr17_even (x := (b : ℤ)) (by exact_mod_cast hb)
    exact ⟨a, c, by rw [h] at he; nlinarith only [he]⟩

private lemma prime17_sq_eight {p : ℕ} (hp : p.Prime) (hbig : 31 < p) (hmod : p % 24 = 17) :
    ∃ a c : ℤ, (p : ℤ) = a ^ 2 + 8 * c ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp8i : (p : ℤ) = 8 * ((p / 8 : ℕ) : ℤ) + 1 := by omega
  have hp8 : (p : ZMod 8) = 1 := by
    have hc := congrArg (fun n : ℤ => (n : ZMod 8)) hp8i
    push_cast at hc
    simpa only [show (8 : ZMod 8) = 0 by decide, zero_mul, zero_add] using hc
  obtain ⟨t, ht⟩ := (ZMod.exists_sq_eq_neg_two_iff (p := p) (by omega)).mpr
    (Or.inl (by omega))
  obtain ⟨a, b, he⟩ := pr17_norm_two hp t (by simpa [pow_two] using ht.symm)
  have hc := congrArg (fun n : ℤ => (n : ZMod 8)) he.symm
  push_cast at hc
  have cert : ∀ i j : ZMod 8, i ^ 2 + 2 * j ^ 2 = 1 → 4 * j = 0 := by decide
  obtain ⟨c, h⟩ := pr17_even (x := b) (cert _ _ (hc.trans hp8))
  exact ⟨a, c, by rw [h] at he; nlinarith only [he]⟩

private lemma prime29_norm {p : ℕ} (hp : p.Prime) (hbig : 31 < p)
    (hmod : p % 120 = 29 ∨ p % 120 = 101) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 5 * b ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp4 : p % 4 = 1 := by omega
  have hp4z : (p : ZMod 4) = 1 := (ZMod.natCast_eq_natCast_iff' p 1 4).mpr (by omega)
  have hp5z : (p : ZMod 5) = 1 ∨ (p : ZMod 5) = 4 := by
    have hr : p % 5 = 1 ∨ p % 5 = 4 := by omega
    rcases hr with hr | hr
    · left
      exact (ZMod.natCast_eq_natCast_iff' p 1 5).mpr (by omega)
    · right
      exact (ZMod.natCast_eq_natCast_iff' p 4 5).mpr (by omega)
  have hpsq : IsSquare (p : ZMod 5) := by
    rcases hp5z with h | h
    · rw [h]
      exact ⟨1, by decide⟩
    · rw [h]
      exact ⟨2, by decide⟩
  have h5sq : IsSquare (5 : ZMod p) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 5) hp4 (by decide)).mpr hpsq
  obtain ⟨i, hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  obtain ⟨j, hj⟩ := h5sq
  have ht : (i * j) ^ 2 = -(5 : ZMod p) := by
    calc
      (i * j) ^ 2 = (i * i) * (j * j) := by ring
      _ = (-1 : ZMod p) * 5 := by rw [← hi, ← hj]
      _ = -5 := by ring
  obtain ⟨x, y, k, hkpos, hklt, he⟩ := small_norm_multiple hp 5 (by decide) (i * j) ht
  norm_num at hklt he
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨x, y, by simpa using he.symm⟩
  · have hc := congrArg (fun n : ℤ => (n : ZMod 5)) he
    push_cast at hc
    have cert : ∀ a b c : ZMod 5,
        (c = 1 ∨ c = 4) → a ^ 2 + 5 * b ^ 2 ≠ c * 2 := by decide
    exact False.elim (cert _ _ _ hp5z hc)
  · have hc := congrArg (fun n : ℤ => (n : ZMod 4)) he
    push_cast at hc
    have cert : ∀ a b c : ZMod 4, c = 1 → a ^ 2 + 5 * b ^ 2 ≠ c * 3 := by decide
    exact False.elim (cert _ _ _ hp4z hc)
  · have hc := congrArg (fun n : ℤ => (n : ZMod 4)) he
    push_cast at hc
    have cert : ∀ a b c : ZMod 4, a ^ 2 + 5 * b ^ 2 = c * 4 →
        2 * a = 0 ∧ 2 * b = 0 := by decide
    have hEven (v : ℤ) (hv : 2 * (v : ZMod 4) = 0) : (2 : ℤ) ∣ v := by
      have hz : ((2 * v : ℤ) : ZMod 4) = 0 := by push_cast; exact hv
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * v) 4).mp hz
      omega
    obtain ⟨ha, hb⟩ := cert _ _ _ hc
    obtain ⟨a, hx⟩ := hEven x ha
    obtain ⟨b, hy⟩ := hEven y hb
    rw [hx, hy] at he
    exact ⟨a, b, by nlinarith only [he]⟩
  · have hc := congrArg (fun n : ℤ => (n : ZMod 5)) he
    push_cast at hc
    have cert : ∀ a b c : ZMod 5, a ^ 2 + 5 * b ^ 2 = c * 5 → a = 0 := by decide
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 5).mp (cert _ _ _ hc)
    rw [hb] at he
    exact ⟨y, b, by nlinarith only [he]⟩

private lemma integer_atoms {n : ℕ} (x y z : ℤ) (b d f : ℕ)
    (h : (n : ℤ) = x^2 * (b : ℤ)^3 + y^2 * (d : ℤ)^3 + z^2 * (f : ℤ)^3) :
    Rep n := by
  refine ⟨x.natAbs^2*b^3, y.natAbs^2*d^3, z.natAbs^2*f^3,
    square_times_cube _ _, square_times_cube _ _, square_times_cube _ _, ?_⟩
  apply Int.ofNat.inj
  push_cast
  simpa [Int.natCast_natAbs, sq_abs] using h.symm

private lemma prime_inert_cast {p : ℕ} (hmod : p % 3 = 2) : (p : ZMod 3) = 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p = 3*k+2 := ⟨p/3, by omega⟩
  rw [hk]
  simp [show (3 : ZMod 3) = 0 by decide]

/-- The signs of the first-plane rotation can be chosen by a three-element calculation. -/
private lemma first_plane_seeds {m : ℕ} (hm : m ∈ ({7, 23, 119} : Finset ℕ)) :
    ∃ x y z : ℤ, (m : ℤ) = x^2+y^2+3*z^2 ∧
      ∀ a c : ZMod 3, a^2+4*c^2=2 →
        (a^2-2*c^2)*(z : ZMod 3)+2*c^2*(x : ZMod 3)+2*a*c*(y : ZMod 3)=0 ∨
        (a^2-2*c^2)*(z : ZMod 3)+2*c^2*(x : ZMod 3)+2*(-a)*c*(y : ZMod 3)=0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨2, 0, 1, by decide, by decide +kernel⟩
  · exact ⟨4, 2, 1, by decide, by decide +kernel⟩
  · exact ⟨10, 4, 1, by decide, by decide +kernel⟩

private lemma first_plane {m p : ℕ} (hm : m ∈ ({7, 23, 119} : Finset ℕ))
    (hmod : p % 3 = 2) (a c : ℤ) (hn : (p : ℤ) = a^2+4*c^2) : Rep (p^2*m) := by
  obtain ⟨x, y, z, he, hs⟩ := first_plane_seeds hm
  have hn3 := congrArg (fun n : ℤ => (n : ZMod 3)) hn
  push_cast at hn3
  have hs3 := hs a c (hn3.symm.trans (prime_inert_cast hmod))
  obtain ⟨t, ht, w, hw⟩ : ∃ t : ℤ, t^2 = a^2 ∧ (3 : ℤ) ∣
      (a^2-2*c^2)*z+2*c^2*x+2*t*c*y := by
    rcases hs3 with h | h
    · refine ⟨a, rfl, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_⟩
      push_cast
      exact h
    · refine ⟨-a, by ring, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_⟩
      push_cast
      exact h
  let X := (t^2+2*c^2)*x+6*c^2*z-2*t*c*y
  let Y := (t^2-4*c^2)*y+2*t*c*(x-3*z)
  have hq : X^2+Y^2+3*((t^2-2*c^2)*z+2*c^2*x+2*t*c*y)^2 =
      (t^2+4*c^2)^2*(x^2+y^2+3*z^2) := by dsimp [X,Y]; ring
  rw [ht, hw, ← hn, ← he] at hq
  apply integer_atoms X Y w 1 1 3
  push_cast
  linear_combination -hq

/-- For the other three kernels the middle coordinate starts even and stays even. -/
private lemma second_plane_seeds {m : ℕ} (hm : m ∈ ({15, 87, 111} : Finset ℕ)) :
    ∃ x s z : ℤ, (m : ℤ) = x^2+8*s^2+3*z^2 ∧
      ∀ a c : ZMod 3, a^2+8*c^2=2 →
        (a^2-4*c^2)*(z : ZMod 3)+4*c^2*(x : ZMod 3)-8*a*c*(s : ZMod 3)=0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨-2, 1, 1, by decide, by decide +kernel⟩
  · exact ⟨2, 1, 5, by decide, by decide +kernel⟩
  · exact ⟨2, 2, 5, by decide, by decide +kernel⟩

private lemma second_plane {m p : ℕ} (hm : m ∈ ({15, 87, 111} : Finset ℕ))
    (hmod : p % 3 = 2) (a c : ℤ) (hn : (p : ℤ) = a^2+8*c^2) : Rep (p^2*m) := by
  obtain ⟨x, s, z, he, hs⟩ := second_plane_seeds hm
  have hn3 := congrArg (fun n : ℤ => (n : ZMod 3)) hn
  push_cast at hn3
  obtain ⟨w, hw⟩ : (3 : ℤ) ∣ (a^2-4*c^2)*z+4*c^2*x-8*a*c*s := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    push_cast
    exact hs a c (hn3.symm.trans (prime_inert_cast hmod))
  let X := (a^2+4*c^2)*x+12*c^2*z+8*a*c*s
  let Y := (a^2-8*c^2)*s+a*c*(3*z-x)
  have hq : X^2+8*Y^2+3*((a^2-4*c^2)*z+4*c^2*x-8*a*c*s)^2 =
      (a^2+8*c^2)^2*(x^2+8*s^2+3*z^2) := by dsimp [X,Y]; ring
  rw [hw, ← hn, ← he] at hq
  apply integer_atoms X Y w 1 2 3
  push_cast
  linear_combination -hq

private lemma third_plane_seeds {m : ℕ} (hm : m ∈ ({15, 87, 111} : Finset ℕ)) :
    ∃ x s z : ℤ, (m : ℤ) = x^2+8*s^2+3*z^2 ∧
      ∀ a b : ZMod 3, a^2+5*b^2=2 →
        (a^2-b^2)*(z : ZMod 3)+8*b^2*(s : ZMod 3)+2*a*b*(x : ZMod 3)=0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨2, -1, 1, by decide, by decide +kernel⟩
  · exact ⟨2, 1, 5, by decide, by decide +kernel⟩
  · exact ⟨2, -2, 5, by decide, by decide +kernel⟩

private lemma third_plane {m p : ℕ} (hm : m ∈ ({15,87,111} : Finset ℕ))
    (hmod : p % 3 = 2) (a b : ℤ) (hn : (p : ℤ) = a^2+5*b^2) : Rep (p^2*m) := by
  obtain ⟨x, s, z, he, hs⟩ := third_plane_seeds hm
  have hn3 := congrArg (fun n : ℤ => (n : ZMod 3)) hn
  push_cast at hn3
  obtain ⟨w, hw⟩ : (3 : ℤ) ∣ (a^2-b^2)*z+8*b^2*s+2*a*b*x := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    push_cast
    exact hs a b (hn3.symm.trans (prime_inert_cast hmod))
  let X := (a^2-5*b^2)*x+2*a*b*(4*s-3*z)
  let Y := (a^2+b^2)*s+3*b^2*z-a*b*x
  have hq : X^2+8*Y^2+3*((a^2-b^2)*z+8*b^2*s+2*a*b*x)^2 =
      (a^2+5*b^2)^2*(x^2+8*s^2+3*z^2) := by dsimp [X,Y]; ring
  rw [hw, ← hn, ← he] at hq
  apply integer_atoms X Y w 1 2 3
  push_cast
  linear_combination -hq

private lemma inert_classes {m p : ℕ} (hm : m ∈ ({7,15,23,87,111,119} : Finset ℕ))
    (hp : p.Prime) (hbig : 31 < p)
    (h : p % 24 = 17 ∨ p % 120 = 29 ∨ p % 120 = 101) : Rep (p^2*m) := by
  have hmod : p % 3 = 2 := by omega
  by_cases hfirst : m ∈ ({7,23,119} : Finset ℕ)
  · obtain ⟨a, c, hn⟩ := prime_four hp (by omega)
    exact first_plane hfirst hmod a c hn
  have hsecond : m ∈ ({15,87,111} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm hfirst ⊢
    omega
  rcases h with h17 | h5
  · obtain ⟨a, c, hn⟩ := prime17_sq_eight hp hbig h17
    exact second_plane hsecond hmod a c hn
  · obtain ⟨a, b, hn⟩ := prime29_norm hp hbig h5
    exact third_plane hsecond hmod a b hn

/-- Inert primes outside the three classes resolved by ternary norm rotations. -/
def H1 : Prop := ∀ m ∈ ({7, 15, 23, 87, 111, 119} : Finset ℕ),
  ∀ p : ℕ, p.Prime → 31 < p → p % 3 = 2 → p % 24 ≠ 17 → p % 120 ≠ 29 → p % 120 ≠ 101 →
    ∃ x y z : ℕ, (x = 0 ∨ IsPowerful x) ∧ (y = 0 ∨ IsPowerful y) ∧
      (z = 0 ∨ IsPowerful z) ∧ x + y + z = p ^ 2 * m

/-- The remaining split primes have a representation by the principal form of discriminant -108. -/
def H2 : Prop := ∀ m ∈ ({7, 15, 23, 87, 111, 119} : Finset ℕ),
  ∀ p : ℕ, p.Prime → 31 < p → (∃ a b : ℤ, (p : ℤ) = a ^ 2 + 27*b ^ 2) →
    ∃ x y z : ℕ, (x = 0 ∨ IsPowerful x) ∧ (y = 0 ∨ IsPowerful y) ∧
      (z = 0 ∨ IsPowerful z) ∧ x + y + z = p ^ 2 * m

theorem main : H1 → H2 → OMA.R_oeis_a056828_R1.H2 := by
  intro inert principal m hm p hp hbig
  have hnodvd : ¬ 3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have hmod0 : p % 3 ≠ 0 := fun h => hnodvd (Nat.dvd_of_mod_eq_zero h)
  by_cases hi : p % 3 = 2
  · by_cases done : p % 24 = 17 ∨ p % 120 = 29 ∨ p % 120 = 101
    · exact inert_classes hm hp hbig done
    · exact inert m hm p hp hbig hi (by tauto) (by tauto) (by tauto)
  obtain ⟨a, b, hn⟩ := split_prime_norm hp hbig (by omega)
  by_cases hb : (b : ZMod 3) = 0
  · obtain ⟨v, hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb
    exact principal m hm p hp hbig ⟨a, v, by rw [hn, hv]; ring⟩
  have ha : (a : ZMod 3) ≠ 0 := by
    intro ha0
    obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha0
    have hd : (3 : ℤ) ∣ (p : ℤ) := ⟨3*u^2+b^2, by rw [hn,hu]; ring⟩
    exact hnodvd (by exact_mod_cast hd)
  exact rotated hm a b hn ha hb

end OMA.R_oeis_a056828_R1_H2_R1

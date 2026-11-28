import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib

/-! The elementary bound for the squarefree ideal coefficients of the reciprocal
Dedekind zeta function. The bound on primes above a rational prime is the
fundamental identity for ramification indices and residue degrees (see
R. Schoof, Algebraic Number Theory, Proposition 6.4).
Reduction by @STARDUSTLC666. Lean proof by @dwilfand-sys. -/

open Filter Asymptotics NumberField
open scoped NumberField

private theorem erh_prime_cover_card (K : Type) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card ≤
      Module.finrank ℤ (𝓞 K) := by
  classical
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hcast : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hJ : J ≠ ⊥ := by simpa [J] using hcast
  letI : J.IsMaximal :=
    ((Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal hJ
  let T := IsDedekindDomain.primesOverFinset J (𝓞 K)
  have hT : (T : Set (Ideal (𝓞 K))) = J.primesOver (𝓞 K) :=
    IsDedekindDomain.coe_primesOverFinset hJ (𝓞 K)
  have hcard : T.card = Fintype.card (J.primesOver (𝓞 K)) := by
    calc
      T.card = Fintype.card (T : Set (Ideal (𝓞 K))) := by simp
      _ = _ := Fintype.card_congr (Equiv.setCongr hT)
  change T.card ≤ _
  rw [hcard, ← Ideal.sum_ramification_inertia_eq_finrank J (𝓞 K)]
  calc
    _ = ∑ _q : J.primesOver (𝓞 K), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun q _ =>
      Nat.mul_pos (q.val.ramificationIdx_pos ℤ) (q.val.inertiaDeg_pos ℤ)

private theorem erh_prime_cover_mem (K : Type) [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (n : ℕ) (hn : n ≠ 0) (hdvd : P.absNorm ∣ n) :
    P ∈ n.primeFactors.biUnion
      (fun p => IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)) := by
  classical
  letI : P.IsMaximal := hP.isMaximal hP0
  obtain ⟨p, f, hf, hmem, hp, hnorm⟩ := P.exists_prime_and_absNorm_eq_pow
  have hpn : p ∣ n := dvd_trans (dvd_pow_self p (Nat.ne_of_gt hf)) (hnorm ▸ hdvd)
  refine Finset.mem_biUnion.mpr ⟨p, hp.mem_primeFactors hpn hn, ?_⟩
  let J : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hcast : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hJ : J ≠ ⊥ := by simpa [J] using hcast
  letI maxJ : J.IsMaximal :=
    ((Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal hJ
  apply (IsDedekindDomain.mem_primesOverFinset_iff hJ (𝓞 K)).mpr
  refine ⟨hP, ⟨maxJ.eq_of_le (hP.comap (algebraMap ℤ (𝓞 K))).ne_top ?_⟩⟩
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
  simpa using hmem

private theorem erh_distinct_factor_bound (c : ℝ) (hc : 1 ≤ c)
    (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → c ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_gt (c ^ ε⁻¹)
  refine ⟨c ^ B, ?_⟩
  intro n hn
  let L := n.primeFactors.filter fun p => p < B
  let H := n.primeFactors.filter fun p => ¬p < B
  have hL : L.card ≤ B := by
    have h : L ⊆ Finset.range B := fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card h
  have hbig (t : Finset ℕ) (ht : ∀ p ∈ t, B ≤ p) :
      c ^ t.card ≤ ((∏ p ∈ t, p : ℕ) : ℝ) ^ ε := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
      have hpB := ht p (Finset.mem_insert_self ..)
      have hcp : c ≤ (p : ℝ) ^ ε :=
        (Real.rpow_inv_le_iff_of_pos (by linarith : 0 ≤ c) (Nat.cast_nonneg p) he).mp
          (hB.le.trans (by exact_mod_cast hpB))
      have hi := ih (fun q hq => ht q (Finset.mem_insert_of_mem hq))
      rw [Finset.card_insert_of_notMem hpt, pow_succ, Finset.prod_insert hpt,
        Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), mul_comm ((p : ℝ)^ε)]
      exact mul_le_mul hi hcp (by linarith) (by positivity)
  have hH := hbig H (fun p hp => Nat.le_of_not_gt (Finset.mem_filter.mp hp).2)
  have hprod : (∏ p ∈ H, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset H n.primeFactors id (Finset.filter_subset _ _)).trans
      n.prod_primeFactors_dvd
  have hpows : ((∏ p ∈ H, p : ℕ) : ℝ) ^ ε ≤ (n : ℝ)^ε :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_of_dvd hn hprod) he.le
  have hcards : L.card + H.card = n.primeFactors.card :=
    Finset.card_filter_add_card_filter_not _
  rw [← hcards, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ hc hL) (hH.trans hpows) (by positivity) (by positivity)

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1.H1 := by
  classical
  intro K _ _ P N a ε hε
  let d := Module.finrank ℤ (𝓞 K)
  obtain ⟨C, hC⟩ := erh_distinct_factor_bound ((2 : ℝ)^d) (one_le_pow₀ (by norm_num)) ε hε
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let U := n.primeFactors.biUnion
    (fun p => IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))
  have hU : U.card ≤ n.primeFactors.card * d :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun p hp =>
      erh_prime_cover_card K p (Nat.prime_of_mem_primeFactors hp))
  let F := N ⁻¹' ({n} : Set ℕ)
  let e : P ↪ Ideal (𝓞 K) := ⟨Subtype.val, Subtype.val_injective⟩
  let enc (S : F) : U.powerset := ⟨S.val.map e, by
    apply Finset.mem_powerset.mpr
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
    have hnorm : Ideal.absNorm p.1 ∣ N S.val := Finset.dvd_prod_of_mem _ hp
    have hSN : N S.val = n := S.property
    exact erh_prime_cover_mem K p.1 p.2.1 p.2.2 n (by omega) (hSN ▸ hnorm)⟩
  have hinj : Function.Injective enc := by
    intro s t h
    apply Subtype.ext
    exact (Finset.map_injective e) (congrArg Subtype.val h)
  letI : Fintype F := Fintype.ofInjective enc hinj
  have hbound : Fintype.card F ≤ 2 ^ U.card := by
    simpa using Fintype.card_le_of_injective enc hinj
  change ‖∑' S : F, (-1 : ℂ)^S.val.card‖ ≤ C * ‖(n : ℝ)^ε‖
  rw [tsum_fintype, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)]
  calc
    _ ≤ ∑ S : F, ‖(-1 : ℂ)^S.val.card‖ := norm_sum_le _ _
    _ = (Fintype.card F : ℝ) := by simp
    _ ≤ ((2 : ℝ)^U.card) := by exact_mod_cast hbound
    _ ≤ (2 : ℝ)^(n.primeFactors.card*d) := pow_le_pow_right₀ (by norm_num) hU
    _ = ((2 : ℝ)^d)^n.primeFactors.card := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := hC n hn

import OMAReductions.R_ResearchErdos142PrimePartialCycle_R1

namespace Erdos142PrimePartialCycle

open Finset Erdos142 OMA.R_ResearchErdos142PrimePartialCycle_R1
  OMA.R_Erdos142_erdos_142_variants_lower_R3

private lemma mem_partialCycle_source {A : Finset ℕ} {p t z : ℕ}
    (hz : z ∈ partialCycle A p t) :
    (∃ e ∈ Ico 1 p, ∃ x ∈ A, z = e + p * (x - 1)) ∨
      ∃ x ∈ A, x % p = t ∧ z = p * x := by
  rw [partialCycle, mem_union] at hz
  rcases hz with hz | hz
  · obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    exact Or.inl ⟨q.1, (mem_product.mp hq).1, q.2, (mem_product.mp hq).2, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact Or.inr ⟨x, (mem_filter.mp hx).1, (mem_filter.mp hx).2, rfl⟩

private lemma decode_mem {A : Finset ℕ} {p t z : ℕ} (hp : 1 < p)
    (hz : z ∈ partialCycle A p t) : (z - 1) / p + 1 ∈ A := by
  rcases mem_partialCycle_source hz with ⟨e, he, x, hx, rfl⟩ | ⟨x, hx, -, rfl⟩
  · have he' := mem_Ico.mp he
    have hxp : 0 < x := by
      by_contra! h
      have : x = 0 := by omega
      subst x
      simp at hx
    have hcalc : (e + p * (x - 1) - 1) / p = x - 1 := by
      rw [show e + p * (x - 1) - 1 = p * (x - 1) + (e - 1) by omega,
        Nat.add_div (p * (x - 1)) (e - 1) p, Nat.mul_div_left]
      have : (e - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
      omega
    simpa [hcalc] using hx
  · have hxp : 0 < x := by
      by_contra! h
      have : x = 0 := by omega
      subst x
      simp at hx
    have hcalc : (p * x - 1) / p = x - 1 := by
      rw [show p * x - 1 = p * (x - 1) + (p - 1) by omega,
        Nat.add_div (p * (x - 1)) (p - 1) p, Nat.mul_div_left]
      have : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
      omega
    simpa [hcalc] using hx

private lemma multiple_source {A : Finset ℕ} {p t z : ℕ} (hp : 1 < p)
    (hz : z ∈ partialCycle A p t) (hzero : z % p = 0) :
    ∃ x ∈ A, x % p = t ∧ z = p * x := by
  rcases mem_partialCycle_source hz with hcore | hextra
  · obtain ⟨e, he, x, hx, rfl⟩ := hcore
    have he' := mem_Ico.mp he
    have : (e + p * (x - 1)) % p = e := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he'.2]
    omega
  · exact hextra

theorem partialCycle_free {A : Finset ℕ} {k p t N : ℕ}
    (hp : 1 < p) (hk : 2 * p ≤ k) (complete : completeResidues p)
    (hA : A ⊆ Icc 1 N) (freeA : (A : Set ℕ).IsAPOfLengthFree k) :
    (partialCycle A p t : Set ℕ).IsAPOfLengthFree k := by
  rw [apFree_iff (by omega)]
  rintro ⟨a, d, hd, hall⟩
  by_cases hdiv : d % p = 0
  · obtain ⟨e, rfl⟩ := Nat.dvd_of_mod_eq_zero hdiv
    have he : 0 < e := by
      by_contra! hz
      have : e = 0 := by omega
      subst e
      simp at hd
    apply (apFree_iff (by omega)).mp freeA
    refine ⟨(a - 1) / p + 1, e, he, fun i hi => ?_⟩
    have hm := decode_mem hp (hall i hi)
    have ha : 0 < a := by
      by_contra! ha
      have : a = 0 := by omega
      subst a
      have hz := mem_partialCycle_source (hall 0 (by omega))
      rcases hz with ⟨q, hq, x, hx, hz⟩ | ⟨x, hx, ht, hz⟩
      · have := (mem_Ico.mp hq).1
        omega
      · have hxpos := (mem_Icc.mp (hA hx)).1
        omega
    have hcalc : (a + i * (p * e) - 1) / p + 1 = (a - 1) / p + 1 + i * e := by
      rw [show a + i * (p * e) - 1 = (a - 1) + p * (i * e) by ring_nf; omega,
        Nat.add_mul_div_left]
      omega
    rwa [hcalc] at hm
  · obtain ⟨i, hi, hzero⟩ := complete a d hdiv
    have hip : i + p < k := by omega
    obtain ⟨x, hx, hxt, hxval⟩ := multiple_source hp (hall i (by omega)) hzero
    have hzero2 : (a + (i + p) * d) % p = 0 := by
      rw [Nat.add_mul, Nat.add_mod, Nat.mul_mod, Nat.add_mod, hzero]
      simp
    obtain ⟨y, hy, hyt, hyval⟩ := multiple_source hp (hall (i + p) hip) hzero2
    have hdiff : y = x + d := by
      rw [hxval, hyval] at *
      have : p * y = p * x + p * d := by omega
      exact Nat.eq_add_of_mul_eq_mul_left (by omega) this
    have hmods : (x + d) % p = x % p := by rw [← hdiff, hyt, hxt]
    have : d % p = 0 := by
      rw [Nat.add_mod] at hmods
      omega
    exact hdiv this

end Erdos142PrimePartialCycle

theorem OMA.solution : OMA.R_ResearchErdos142PrimePartialCycle_R1.H1 := by
  intro A k p t N hp hk complete hA freeA
  exact Erdos142PrimePartialCycle.partialCycle_free hp hk complete hA freeA


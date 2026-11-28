import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R5
import Mathlib

/-! Same-parameter prime-square costs in the intermediate A085265 and A085267 sieve. -/

namespace A085265.SameJ

open Finset

def oddPrimes (x : ℕ) : Finset ℕ := (range (x+1)).filter (fun p => 2 < p ∧ p.Prime)
def active (J : ℕ) : Finset ℕ := (oddPrimes (2*J+1)).filter (fun p => p^2 ≤ 2*J)
def recip (A : Finset ℕ) : ℚ := ∑ p ∈ A, 1/(p:ℚ)^2

private lemma recip_mono {A B : Finset ℕ} (h : A ⊆ B) : recip A ≤ recip B :=
  sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

theorem mask_active {J : ℕ} {A : Finset ℕ} (hJ : 300 ≤ J)
    (hA : A ⊆ {3,5,7,11,13,17}) : A ⊆ active J := by
  intro p hp
  have tab : ∀ q ∈ ({3,5,7,11,13,17} : Finset ℕ), 2 < q ∧ q.Prime ∧ q ≤ 17 := by decide
  obtain ⟨h2,hprime,hle⟩ := tab p (hA hp)
  have sq := Nat.pow_le_pow_left hle 2
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), h2, hprime⟩, by omega⟩

theorem cost {J : ℕ} {S A : Finset ℕ} {α R : ℚ} (haS : A ⊆ S)
    (ha : A ⊆ active J) (hc : ((oddPrimes (2*J+1)).card : ℚ) ≤ α*(J:ℚ))
    (hr : recip (active J) ≤ R) :
    ((∑ p ∈ oddPrimes (2*J+1) \ S, 2*J/(p^2)+1 : ℕ) : ℚ) ≤
      (J:ℚ)*(α+2*(R-recip A))-(A.card:ℚ) := by
  let P := oddPrimes (2*J+1)
  let E := P \ S
  let B := E.filter (fun p => p^2 ≤ 2*J)
  have out {p : ℕ} (hp : p ∈ E) : p ∉ A :=
    fun h => (mem_sdiff.mp hp).2 (haS h)
  have disj : Disjoint E A := disjoint_left.mpr fun _ hp => out hp
  have bdisj : Disjoint B A := disjoint_left.mpr fun _ hp => out (mem_filter.mp hp).1
  have esub : E ∪ A ⊆ P := union_subset sdiff_subset (fun _ h => (mem_filter.mp (ha h)).1)
  have bsub : B ∪ A ⊆ active J := by
    apply union_subset _ ha
    intro p hp
    obtain ⟨he, hs⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_sdiff.mp he).1, hs⟩
  have rsum : recip B + recip A ≤ R := by
    calc
      _ = recip (B ∪ A) := (sum_union bdisj).symm
      _ ≤ _ := (recip_mono bsub).trans hr
  have csum : (E.card:ℚ) + (A.card:ℚ) ≤ α*(J:ℚ) := by
    have cn : E.card + A.card ≤ P.card := by
      rw [← card_union_of_disjoint disj]
      exact card_le_card esub
    exact (show (E.card:ℚ) + (A.card:ℚ) ≤ (P.card:ℚ) by exact_mod_cast cn).trans hc
  have remove : (∑ p ∈ B, 2*J/(p^2)) = ∑ p ∈ E, 2*J/(p^2) := by
    apply sum_subset (filter_subset _ _)
    intro p hp hn
    exact Nat.div_eq_of_lt (lt_of_not_ge (fun hs => hn (mem_filter.mpr ⟨hp,hs⟩)))
  have hf : ((∑ p ∈ E, 2*J/(p^2) : ℕ) : ℚ) ≤ 2*(J:ℚ)*(R-recip A) := by
    rw [← remove, Nat.cast_sum]
    calc
      _ ≤ ∑ p ∈ B, 2*(J:ℚ)*(1/(p:ℚ)^2) := by
        apply sum_le_sum
        intro p hp
        have hp0 : 0 < p := by
          have hodd := (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2.1
          omega
        rw [mul_one_div]
        apply (le_div_iff₀ (show 0 < (p:ℚ)^2 by positivity)).mpr
        exact_mod_cast Nat.div_mul_le_self (2*J) (p^2)
      _ = 2*(J:ℚ)*recip B := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [rsum]) (by positivity)
  change ((∑ p ∈ E, 2*J/(p^2)+1 : ℕ) : ℚ) ≤ _
  rw [sum_add_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_add]
  calc
    _ ≤ 2*(J:ℚ)*(R-recip A) + (α*(J:ℚ)-(A.card:ℚ)) :=
      add_le_add hf (by linarith only [csum])
    _ = _ := by ring

private theorem active_recip_of_hi {J H T : ℕ} (hJ : J ≤ H) (hT : 2*H < (T+1)^2) :
    recip (active J) ≤ recip (oddPrimes T) := by
  apply recip_mono
  intro p hp
  obtain ⟨hmem,hs⟩ := mem_filter.mp hp
  have hle : p ≤ T := by
    by_contra! hh
    have bound := Nat.pow_le_pow_left (show T+1 ≤ p by omega) 2
    omega
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hmem).2⟩

theorem active_recip_420 {J : ℕ} (h : J ≤ 420) : recip (active J) ≤ 96911/500000 :=
  (active_recip_of_hi (T := 28) h (by decide)).trans (by decide +kernel)

theorem active_recip_599 {J : ℕ} (h : J ≤ 599) : recip (active J) ≤ 49013/250000 :=
  (active_recip_of_hi (T := 34) h (by decide)).trans (by decide +kernel)

theorem active_recip_1023 {J : ℕ} (h : J ≤ 1023) : recip (active J) ≤ 98959/500000 :=
  (active_recip_of_hi (T := 45) h (by decide)).trans (by decide +kernel)

theorem active_recip_2047 {J : ℕ} (h : J ≤ 2047) : recip (active J) ≤ 199283/1000000 :=
  (active_recip_of_hi (T := 63) h (by decide)).trans (by decide +kernel)

theorem active_recip_4095 {J : ℕ} (h : J ≤ 4095) : recip (active J) ≤ 200323/1000000 :=
  (active_recip_of_hi (T := 90) h (by decide)).trans (by decide +kernel)

private theorem odd_reciprocal_step {p T : ℕ} (hT : 1 ≤ T) (hTp : T < p) :
    1/(p : ℚ)^2 + 1/(2*((p : ℚ)+1)) ≤ 1/(2*(T : ℚ)) := by
  have hpos : (0 : ℚ) < T := by exact_mod_cast (show 0 < T by omega)
  have hle : (T : ℚ)+1 ≤ p := by exact_mod_cast (show T+1 ≤ p by omega)
  have hm : 0 < (p : ℚ)-1 := by linarith
  have hp : 0 < (p : ℚ)+1 := by positivity
  have htel : 1/(2*((p : ℚ)-1)) - 1/(2*((p : ℚ)+1)) =
      1/(((p : ℚ)-1)*((p : ℚ)+1)) := by
    field_simp [hm.ne', hp.ne'] <;> ring
  have hrec : 1/(p : ℚ)^2 ≤ 1/(((p : ℚ)-1)*((p : ℚ)+1)) :=
    one_div_le_one_div_of_le (mul_pos hm hp) (by nlinarith)
  have hstart : 1/(2*((p : ℚ)-1)) ≤ 1/(2*(T : ℚ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

private theorem odd_reciprocal_tail_aux (count : ℕ) (P : Finset ℕ)
    (hcard : P.card = count) (T : ℕ) (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) := by
  induction count generalizing P T with
  | zero =>
    have he := Finset.card_eq_zero.mp hcard
    subst P
    simp only [Finset.sum_empty]
    positivity
  | succ count ih =>
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    let p := P.min' hne
    have hp : p ∈ P := P.min'_mem hne
    have hcard' : (P.erase p).card = count := by
      rw [Finset.card_erase_of_mem hp, hcard] <;> omega
    have hsub {q : ℕ} (hq : q ∈ P.erase p) : q ∈ P := (Finset.mem_erase.mp hq).2
    have hnext (q : ℕ) (hq : q ∈ P.erase p) : p+1 < q := by
      have hdiff := (Finset.mem_erase.mp hq).1
      have hmin : p ≤ q := P.min'_le q (hsub hq)
      obtain ⟨hp2,hpp⟩ := hP p hp
      obtain ⟨hq2,hqp⟩ := hP q (hsub hq)
      obtain ⟨i,hi⟩ := hpp.odd_of_ne_two (by omega)
      obtain ⟨j,hj⟩ := hqp.odd_of_ne_two (by omega)
      omega
    have htail := ih (P.erase p) hcard' (p+1) (by omega)
      (fun q hq => hP q (hsub hq)) hnext
    rw [← Finset.add_sum_erase P (fun q => 1/(q : ℚ)^2) hp]
    calc
      _ ≤ 1/(p : ℚ)^2 + 1/(2*(((p+1 : ℕ) : ℚ))) := add_le_add_left htail _
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using
        odd_reciprocal_step hT (hcut p hp)

/-- A finite subset of the odd primes past `T` has reciprocal-square sum at
most `1/(2T)`, by telescoping along successive odd integers. -/
theorem oddPrimeReciprocalTail {P : Finset ℕ} {T : ℕ} (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) :=
  odd_reciprocal_tail_aux P.card P rfl T hT hP hcut

theorem active_recip_global (J : ℕ) : recip (active J) ≤ 41/200 := by
  let Q := active J
  let low := Q.filter (fun p => p ≤ 128)
  let high := Q.filter (fun p => ¬p ≤ 128)
  have prop (p : ℕ) (hp : p ∈ Q) : 2 < p ∧ p.Prime :=
    (mem_filter.mp (mem_filter.mp hp).1).2
  have sub : low ⊆ oddPrimes 128 := by
    intro p hp
    obtain ⟨hq,hle⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), prop p hq⟩
  have tail : recip high ≤ 1/(2*(128:ℚ)) :=
    oddPrimeReciprocalTail (by decide) (fun p hp => prop p (mem_filter.mp hp).1)
      (fun _ hp => lt_of_not_ge (mem_filter.mp hp).2)
  have partition : recip low + recip high = recip Q :=
    sum_filter_add_sum_filter_not Q (fun p => p ≤ 128) (fun p => 1/(p:ℚ)^2)
  have finite : recip (oddPrimes 128) + 1/(2*(128:ℚ)) ≤ 41/200 := by decide +kernel
  exact partition ▸ (add_le_add (recip_mono sub) tail).trans finite

end A085265.SameJ

theorem OMA.solution : OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R5.H1 := by
  intro J S A α R hJ hc
  obtain ⟨ha,hm,hc,hr⟩ := hc
  apply A085265.SameJ.cost ha (A085265.SameJ.mask_active hJ hm) hc
  rcases hr with ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | rfl
  · exact A085265.SameJ.active_recip_420 h
  · exact A085265.SameJ.active_recip_599 h
  · exact A085265.SameJ.active_recip_1023 h
  · exact A085265.SameJ.active_recip_2047 h
  · exact A085265.SameJ.active_recip_4095 h
  · exact A085265.SameJ.active_recip_global J

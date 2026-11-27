import OMAReductions.R_Green31_green_31_variants_abelian_R1
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.Bertrand

/-!
The Bose–Chowla construction in a quadratic finite field gives a Sidon set
of size p in the range p²−1. Bertrand's postulate interpolates between sizes.
The short discrete-log argument is adapted from @amp2600's Bose–Chowla
section in open-math-agents PR #1911. The two-element recovery lemma is
from @loris-olsem's parent reduction in PR #8646.
-/

open OMA.R_Green31_green_31_variants_abelian_R1

private theorem shortLog {G : Type*} [Group G] [Finite G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (u : G) :
    ∃ n : ℕ, n < Nat.card G ∧ g ^ n = u := by
  obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hg u)
  refine ⟨n % orderOf g, ?_, (pow_mod_orderOf g n).trans hn⟩
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.mod_lt _ (orderOf_pos g)

private theorem primeSidon (p : ℕ) (hp : p.Prime) :
    ∃ A : Finset ℕ, A ⊆ Finset.range (p ^ 2 - 1) ∧
      IsSidon (A : Set ℕ) ∧ A.card = p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := ZMod p
  let K := GaloisField p 2
  let : Field F := inferInstanceAs (Field (ZMod p))
  let : Field K := inferInstanceAs (Field (GaloisField p 2))
  let : Algebra F K := inferInstanceAs (Algebra (ZMod p) (GaloisField p 2))
  let : Finite K := inferInstanceAs (Finite (GaloisField p 2))
  let : Fintype F := ZMod.fintype p
  let : Fintype K := Fintype.ofFinite K
  let i := algebraMap F K
  have hK : Nat.card K = p ^ 2 := GaloisField.card p 2 (by decide)
  have hF : Fintype.card F = p := ZMod.card p
  have hproper : ¬ Function.Surjective i := by
    intro hs
    have h := Fintype.card_le_of_surjective i hs
    rw [← Nat.card_eq_fintype_card (α := K), hK, hF] at h
    exact (not_lt_of_ge h) (by
      simpa only [pow_two, mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos)
  obtain ⟨θ, hθ⟩ : ∃ θ : K, ∀ x : F, i x ≠ θ := by
    simpa only [Function.Surjective, not_forall, not_exists] using hproper
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgu : Nat.card Kˣ = p ^ 2 - 1 := by rw [Nat.card_units, hK]
  have witness (x : F) : ∃ n : ℕ, n < p ^ 2 - 1 ∧ (g : K) ^ n = θ - i x := by
    obtain ⟨n, hn, he⟩ := shortLog g hg (Units.mk0 (θ - i x) (sub_ne_zero.mpr (hθ x).symm))
    exact ⟨n, hgu ▸ hn, by simpa using congrArg Units.val he⟩
  choose e he hpow using witness
  have hinj : Function.Injective e := by
    intro x y h
    apply i.injective
    apply sub_right_inj.mp
    exact (hpow x).symm.trans ((congrArg (fun n : ℕ => (g : K) ^ n) h).trans (hpow y))
  refine ⟨Finset.univ.image e, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (he x)
  · intro a ha c hc b hb d hd hsum
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hd
    have hprod : (θ - i x) * (θ - i y) = (θ - i z) * (θ - i w) := by
      calc
        _ = (g : K) ^ (e x + e y) := by rw [pow_add, hpow, hpow]
        _ = (g : K) ^ (e z + e w) := congrArg _ hsum
        _ = _ := by rw [pow_add, hpow, hpow]
    have hlin : θ * i ((x+y)-(z+w)) = i (x*y-z*w) := by
      simp only [map_sub, map_mul, map_add]
      linear_combination -hprod
    have hs : x + y = z + w := by
      by_contra hn
      have hnon : i ((x+y)-(z+w)) ≠ 0 := by
        exact (map_ne_zero i).mpr (sub_ne_zero.mpr hn)
      apply hθ ((x*y-z*w) / ((x+y)-(z+w)))
      rw [map_div₀]
      exact (div_eq_iff hnon).mpr hlin.symm
    have hpairs : x*y = z*w := by
      apply i.injective
      have hs' : i (x + y) = i (z + w) := congrArg i hs
      simp only [map_add] at hs'
      simp only [map_mul]
      linear_combination hprod + θ * hs'
    rcases recover_pair hs hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hF]

theorem OMA.solution : OMA.R_Green31_green_31_variants_abelian_R1.H1 := by
  intro L hL
  by_cases hsmall : L ≤ 4
  · refine ⟨{0}, ?_, ?_, by simpa using hsmall⟩
    · intro x hx
      obtain rfl := Finset.mem_singleton.mp hx
      exact Finset.mem_range.mpr hL
    · intro a ha c hc b hb d hd _
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hc hb hd
      exact Or.inl ⟨ha.trans hc.symm, hb.trans hd.symm⟩
  let n := L.sqrt / 2
  have hlow : L.sqrt ^ 2 ≤ L := (Nat.le_sqrt').mp le_rfl
  have hhigh : L < (L.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' L
  have hsqrt : 2 ≤ L.sqrt := (Nat.le_sqrt').mpr (by omega)
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n (by dsimp [n]; omega)
  have hps : p ≤ L.sqrt := by dsimp [n] at hpn; omega
  have hsp : L.sqrt + 1 ≤ 2*p := by dsimp [n] at hnp; omega
  obtain ⟨A, hA, hSid, hcard⟩ := primeSidon p hp
  refine ⟨A, ?_, hSid, ?_⟩
  · exact hA.trans (Finset.range_mono (by
      have := Nat.pow_le_pow_left hps 2
      omega))
  · rw [hcard]
    calc
      L ≤ (L.sqrt + 1) ^ 2 := hhigh.le
      _ ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left hsp 2
      _ = 4 * p ^ 2 := by ring

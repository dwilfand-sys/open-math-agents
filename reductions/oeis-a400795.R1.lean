import OMAStatements.S_oeis_a400795
import Mathlib

/-!
Source: https://oeis.org/A400795
Petersen, Validashti and Wayland defined the exceptional set. This reduction
follows the prime and large-gcd arguments in the A400795 research manuscripts
at dwilfand-sys/open-math-agents, commit 5d37e98de434449bfaf25b6919061e3d5d4cd9f4.
Credit: @dwilfand-sys

For infinitude, candidate primes impose local conditions which force every
representation to have a large gcd. A separate sieve estimate supplies
candidates avoiding all triples in the resulting factor equation.
For density, a suitable prime divisor of n+1 constructs an explicit pair.
-/

namespace OMA.R_oeis_a400795_R1

open OMA.S_oeis_a400795

def H1 : Prop :=
  ∀ p a b y : ℕ, p.Prime → 3 < p → p % 3 = 1 →
    (∀ d : ℕ, d ∣ 4*p+1 → d % 4 ≠ 3) →
    (∀ d : ℕ, 1 < d → d ≤ y → ¬ d ∣ 2*p-1) →
    1 < a → 1 < b → triangleCount a b = 2*p-1 →
    y < a.gcd b ∧ ∃ u v : ℕ, 0 < u ∧ 0 < v ∧
      2*(2*p-1) = (a.gcd b)^2*(u*v) + (a.gcd b)*(u+v-1)

/-- Select candidates outside the count of positive large-gcd triples. -/
def H2 : Prop :=
  ∀ B : ℕ, ∃ p y : ℕ, B < p ∧ p.Prime ∧ 3 < p ∧ p % 3 = 1 ∧
    (∀ d : ℕ, d ∣ 4*p+1 → d % 4 ≠ 3) ∧
    (∀ d : ℕ, 1 < d → d ≤ y → ¬ d ∣ 2*p-1) ∧
    ∀ g u v : ℕ, y < g → 0 < u → 0 < v →
      2*(2*p-1) ≠ g^2*(u*v) + g*(u+v-1)

def H3 : Prop :=
  ∀ n q : ℕ, q.Prime → 2 < q → q < n+1 → q ∣ n+1 →
    Nat.Coprime (q-1) (2*n+1) →
    1 < q-1 ∧ 1 < 2*((n+1)/q)-1 ∧
      triangleCount (q-1) (2*((n+1)/q)-1) = n

def H4 : Prop :=
  let witnesses := fun n : ℕ => (Finset.range (n+1)).filter fun q =>
    q.Prime ∧ 2 < q ∧ q ∣ n+1 ∧ Nat.Coprime (q-1) (2*n+1)
  let miss := fun N : ℕ => ((Finset.Icc 1 N).filter fun n => witnesses n = ∅).card
  Filter.Tendsto (fun N : ℕ => (miss N : ℝ) / (N : ℝ)) Filter.atTop (nhds 0)

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a400795.main := by
  intro obstruction primeSieve witness residueSieve
  constructor
  · intro finite
    obtain ⟨B,hB⟩ := finite.bddAbove
    obtain ⟨p,y,hBp,hp,hp3,hmod,hsplit,hrough,hnone⟩ := primeSieve B
    have hm : 2*p-1 ∈ stronglyNontriangular := by
      refine ⟨by omega, by omega, ?_⟩
      rintro ⟨a,b,ha,hb,ht⟩
      obtain ⟨hg,u,v,hu,hv,he⟩ := obstruction p a b y hp hp3 hmod hsplit hrough ha hb ht
      exact hnone (a.gcd b) u v hg hu hv he
    have hle : 2*p-1 ≤ B := hB hm
    omega
  · let W := fun n : ℕ => (Finset.range (n+1)).filter fun q =>
      q.Prime ∧ 2 < q ∧ q ∣ n+1 ∧ Nat.Coprime (q-1) (2*n+1)
    let miss := fun N : ℕ => ((Finset.Icc 1 N).filter fun n => W n = ∅).card
    have hlim : Filter.Tendsto (fun N : ℕ => (miss N : ℝ) / (N : ℝ))
        Filter.atTop (nhds 0) := residueSieve
    have hcard (N : ℕ) : initialCount N ≤ miss N := by
      classical
      change ((Finset.Icc 1 N).filter fun n => n ∈ stronglyNontriangular).card ≤
        ((Finset.Icc 1 N).filter fun n => W n = ∅).card
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hr,hexc⟩ := Finset.mem_filter.mp hn
      apply Finset.mem_filter.mpr
      refine ⟨hr,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
      intro q hq
      obtain ⟨hqr,hp,hgt,hd,hcop⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha,hb,ht⟩ := witness n q hp hgt (Finset.mem_range.mp hqr) hd hcop
      exact hexc.2.2 ⟨q-1, 2*((n+1)/q)-1, ha, hb, ht⟩
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds hlim
    · intro N
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro N
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard N) (Nat.cast_nonneg _)

end OMA.R_oeis_a400795_R1

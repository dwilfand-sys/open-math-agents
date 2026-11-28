import FormalConjectures.ErdosProblems.«357»

/-!
# Reduction of the reciprocal-summability variant to sparse gaps

Source: https://www.erdosproblems.com/357
Credit: @dwilfand-sys

Codex observed that consecutive grouping preserves distinct interval sums.
Grouping a divergent positive reciprocal series in successively longer
constant-width epochs preserves divergence while making adjacent grouped sums
separate by quantities tending to infinity. Thus it is enough to prove the
conjecture for this sparse subclass.
-/

namespace OMA.R_Erdos357_erdos_357_variants_infinite_set_sum_R1

/-- Every divergent admissible ruler has a divergent admissible coarsening
whose consecutive gaps tend to infinity. -/
def H1 : Prop := ∀ A : ℕ → ℕ, StrictMono A → Erdos357.HasDistinctSums A →
  ¬ Summable (fun j => (1 : ℝ) / A j) →
  ∃ B : ℕ → ℕ, StrictMono B ∧ Erdos357.HasDistinctSums B ∧
    (∀ d : ℕ, ∃ n : ℕ, ∀ j ≥ n, d ≤ B (j + 1) - B j) ∧
    ¬ Summable (fun j => (1 : ℝ) / B j)

/-- The remaining conjecture restricted to rulers whose consecutive gaps
tend to infinity. -/
def H2 : Prop := ∀ B : ℕ → ℕ, StrictMono B → Erdos357.HasDistinctSums B →
  (∀ d : ℕ, ∃ n : ℕ, ∀ j ≥ n, d ≤ B (j + 1) - B j) →
  Summable (fun j => (1 : ℝ) / B j)

theorem main : H1 → H2 →
    type_of% @Erdos357.erdos_357.variants.infinite_set_sum := by
  intro h1 h2 A hmono hdistinct
  by_contra hdiv
  obtain ⟨B, hBmono, hBdistinct, hgaps, hBdiv⟩ :=
    h1 A hmono hdistinct hdiv
  exact hBdiv (h2 B hBmono hBdistinct hgaps)

end OMA.R_Erdos357_erdos_357_variants_infinite_set_sum_R1

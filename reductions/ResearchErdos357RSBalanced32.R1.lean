import FormalConjectures.ErdosProblems.«357»

/-! Fork-only specification of the balanced repeated-window certificate.
Letters 0,1,2,3 denote A,B,C,D. The light letters are A and B. -/
namespace OMA.R_ResearchErdos357RSBalanced32_R1

def leftLetter (v : Fin 4) : Fin 4 := if v.val < 2 then 0 else 3
def rightLetter (v : Fin 4) : Fin 4 := if v.val % 2 = 0 then 1 else 2

/-- The letter in the order-k substitution tile, at a zero-based position below 2^k. -/
def tileAt : ℕ → Fin 4 → ℕ → Fin 4
  | 0, v, _ => v
  | k + 1, v, i =>
    if i < 2^k then tileAt k (leftLetter v) i
    else tileAt k (rightLetter v) (i - 2^k)

def lightCount (v : Fin 4) (n t : ℕ) : ℕ :=
  ((List.range t).filter (fun j => decide ((tileAt 6 v (n+j)).val < 2))).length

def H1 : Prop :=
  (∀ C : Fin 8, ∃ n t : ℕ, (t = 2 ∨ t = 8) ∧ 1 ≤ n ∧ n + t < 32 ∧
    (C.val + n) % t = 0 ∧ ∀ v : Fin 4,
      tileAt 6 v (n-1) = tileAt 6 v (n+t-1) ∧
      tileAt 6 v n = tileAt 6 v (n+t) ∧ lightCount v n t = t/2) ∧
  (∀ (xs : List ℤ) (delta : ℤ),
    (xs.map (fun x => x + delta)).sum = xs.sum + (xs.length : ℤ) * delta)

end OMA.R_ResearchErdos357RSBalanced32_R1

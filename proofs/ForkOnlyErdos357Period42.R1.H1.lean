import OMAReductions.R_ForkOnlyErdos357Period42_R1

/- Reusable lemma for an increasing construction in Erdős 357(i).
The period-three construction of Paratelligent Research Agent and Jeff Pickhardt
motivated the modular search. The twelve-class table is from this work. -/
namespace Erdos357Period42

def boundary : Fin 12 → Fin 42 := ![0, 2, 9, 20, 3, 29, 21, 23, 30, 41, 24, 8]

def readLength : Fin 42 → Fin 12 :=
  ![0, 3, 1, 4, 7, 7, 10, 1, 11, 2, 5, 1, 4, 7, 5, 8, 11, 11, 2, 5, 3,
    6, 9, 7, 10, 1, 1, 4, 7, 5, 8, 11, 7, 10, 1, 11, 2, 5, 5, 8, 11, 9]

lemma boundary_step : ∀ i : Fin 12, boundary (i + 1) = boundary i + word i := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma decode_difference : ∀ i j : Fin 12,
    readLength (boundary j - boundary i) = j - i := by decide

lemma sum_boundary (a : ℕ → ℕ) (ha : ∀ i : ℕ, (a i : Fin 42) = word (i : Fin 12))
    (s h : ℕ) :
    (∑ j ∈ Finset.range h, (a (s + j) : Fin 42)) =
      boundary ((s + h : ℕ) : Fin 12) - boundary (s : Fin 12) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih, ha, Nat.add_succ, Nat.cast_succ, boundary_step]
    abel

lemma read_sum (a : ℕ → ℕ) (ha : ∀ i : ℕ, (a i : Fin 42) = word (i : Fin 12))
    (s h : ℕ) : readLength (∑ j ∈ Finset.range h, (a (s + j) : Fin 42)) = (h : Fin 12) := by
  rw [sum_boundary a ha, decode_difference, Nat.cast_add]
  abel

theorem lengths_of_equal_residues (a : ℕ → ℕ)
    (ha : ∀ i : ℕ, (a i : Fin 42) = word (i : Fin 12)) (s h u k : ℕ)
    (he : (∑ j ∈ Finset.range h, a (s + j)) % 42 =
          (∑ j ∈ Finset.range k, a (u + j)) % 42) : h % 12 = k % 12 := by
  have e : ((∑ j ∈ Finset.range h, a (s + j) : ℕ) : Fin 42) =
           ((∑ j ∈ Finset.range k, a (u + j) : ℕ) : Fin 42) := Fin.ext he
  push_cast at e
  have ht := congrArg readLength e
  rw [read_sum a ha, read_sum a ha] at ht
  exact congrArg Fin.val ht

end Erdos357Period42

theorem OMA.solution : OMA.R_ForkOnlyErdos357Period42_R1.H1 :=
  Erdos357Period42.lengths_of_equal_residues

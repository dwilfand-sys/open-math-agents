import OMAStatements.S_mo_40662
import Mathlib

/-!
# The symplectic block identity over the two-element field

Robert Gunning posed the question. Claude Code supplied the affirmative
argument using the Arf invariant of the split quadratic form. The proof
below uses its characteristic-two diagonal cancellation directly in a trace
calculation: for K = BᵀC, the sum equals tr(K + K²).

Source: https://mathoverflow.net/questions/40662/symplectic-matrices
Credit: @dwilfand-sys (Claude Code, mathematical argument; Codex, trace proof and formalization)
-/

namespace GunningSymplectic

open Finset Matrix

private lemma diagonal_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ι → ZMod 2) (hs : ∀ i j, f i j = f j i) :
    (∑ i ∈ s, ∑ j ∈ s, f i j) = ∑ i ∈ s, f i i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [sum_insert hi, sum_add_distrib, ih]
    have e : (∑ j ∈ s, f j i) = ∑ j ∈ s, f i j :=
      sum_congr rfl fun j _ => hs j i
    rw [e]
    linear_combination CharTwo.add_self_eq_zero (∑ j ∈ s, f i j)

private lemma diag_trace {n : ℕ} (S T : Matrix (Fin n) (Fin n) (ZMod 2))
    (hS : Sᵀ = S) (hT : Tᵀ = T) :
    (∑ i, S i i * T i i) = (S * T).trace := by
  change _ = ∑ i, ∑ j, S i j * T j i
  apply Eq.symm
  apply diagonal_sum
  intro i j
  have hs : S i j = S j i := congrArg (fun X : Matrix _ _ _ => X j i) hS
  have ht : T j i = T i j := congrArg (fun X : Matrix _ _ _ => X i j) hT
  rw [hs, ht]

private lemma trace_square {n : ℕ} (K : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (K * K).trace = K.trace := by
  change (∑ i, ∑ j, K i j * K j i) = ∑ i, K i i
  calc
    _ = ∑ i, K i i * K i i :=
      diagonal_sum univ (fun i j => K i j * K j i) (fun i j => mul_comm _ _)
    _ = _ := by
      have sq : ∀ a : ZMod 2, a*a = a := by decide
      exact sum_congr rfl fun i _ => sq (K i i)

theorem block_identity (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup (Fin n) (ZMod 2)) :
    (∑ i, ∑ j, ∑ k, A i j * B i j * C i k * D i k) = 0 := by
  have ht : fromBlocks Aᵀ Cᵀ Bᵀ Dᵀ ∈ symplecticGroup (Fin n) (ZMod 2) := by
    simpa only [fromBlocks_transpose] using SymplecticGroup.transpose_mem h
  have row := SymplecticGroup.fromBlocks_mem_iff.mp ht
  simp only [transpose_transpose] at row
  have hs : (A * Bᵀ)ᵀ = A * Bᵀ := by
    simpa only [transpose_mul, transpose_transpose] using row.1.symm
  have hv : (C * Dᵀ)ᵀ = C * Dᵀ := by
    simpa only [transpose_mul, transpose_transpose] using row.2.1.symm
  have col := (SymplecticGroup.fromBlocks_mem_iff.mp h).2.2
  have cross : Dᵀ * A = 1 + Bᵀ * C := by
    apply sub_eq_iff_eq_add.mp
    have e := congrArg (fun X : Matrix (Fin n) (Fin n) (ZMod 2) => Xᵀ) col
    change (Aᵀ * D - Cᵀ * B)ᵀ = (1 : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ at e
    simpa only [transpose_sub, transpose_mul, transpose_transpose, transpose_one] using e
  calc
    _ = ∑ i, (A * Bᵀ) i i * (C * Dᵀ) i i := by
      apply sum_congr rfl
      intro i _
      change (∑ j, ∑ k, A i j * B i j * C i k * D i k) =
        (∑ j, A i j * B i j) * (∑ k, C i k * D i k)
      rw [sum_mul]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      exact sum_congr rfl fun k _ => mul_assoc _ _ _
    _ = ((A * Bᵀ) * (C * Dᵀ)).trace := diag_trace _ _ hs hv
    _ = (A * ((Bᵀ * C) * Dᵀ)).trace := by simp only [Matrix.mul_assoc]
    _ = (((Bᵀ * C) * Dᵀ) * A).trace := Matrix.trace_mul_comm _ _
    _ = ((Bᵀ * C) * (Dᵀ * A)).trace := by rw [Matrix.mul_assoc]
    _ = 0 := by
      rw [cross, mul_add, mul_one, Matrix.trace_add, trace_square, CharTwo.add_self_eq_zero]

end GunningSymplectic

theorem OMA.solution : type_of% @OMA.S_mo_40662.main :=
  GunningSymplectic.block_identity

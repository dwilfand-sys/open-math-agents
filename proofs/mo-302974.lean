import OMAStatements.S_mo_302974
import Mathlib

/-!
# mo-302974: Witt vectors of the dual numbers over ZMod p have p-torsion

Take `R = (ZMod p)[ε] / (ε ^ 2)`, the dual numbers over `ZMod p`, and `x` the Teichmüller lift of
`ε`. Then `x ≠ 0`, because its first coefficient is `ε`. In characteristic `p`, multiplication by
`p` on Witt vectors is Verschiebung after Frobenius, and Frobenius raises every coefficient to the
power `p`. The coefficients of `x` are `ε, 0, 0, …` and `ε ^ p = 0`, so the Frobenius of `x` is
`0` and `p * x = 0`. More generally any non-reduced ring of characteristic `p` works.

Proof found by Claude Code (claude-fable-5-2) for @dwilfand-sys.
-/

theorem OMA.solution : type_of% @OMA.S_mo_302974.main := by
  intro p hp
  have hchar : CharP (TrivSqZeroExt (ZMod p) (ZMod p)) p :=
    charP_of_injective_algebraMap (R := ZMod p)
      (by rw [TrivSqZeroExt.algebraMap_eq_inl]; exact TrivSqZeroExt.inl_injective) p
  refine ⟨TrivSqZeroExt (ZMod p) (ZMod p), inferInstance, ?_⟩
  have he0 : (TrivSqZeroExt.inr 1 : TrivSqZeroExt (ZMod p) (ZMod p)) ≠ 0 := by
    intro h
    have h' := congrArg TrivSqZeroExt.snd h
    simp at h'
  have hep : (TrivSqZeroExt.inr 1 : TrivSqZeroExt (ZMod p) (ZMod p)) ^ p = 0 := by
    have h2 : (TrivSqZeroExt.inr 1 : TrivSqZeroExt (ZMod p) (ZMod p)) ^ 2 = 0 := by
      simp [sq]
    exact pow_eq_zero_of_le hp.out.two_le h2
  refine ⟨WittVector.teichmuller p (TrivSqZeroExt.inr 1), ?_, ?_⟩
  · intro h
    apply he0
    have h' := congrArg (fun w => WittVector.coeff w 0) h
    simpa using h'
  · have hfrob : WittVector.frobenius (WittVector.teichmuller p
        (TrivSqZeroExt.inr 1 : TrivSqZeroExt (ZMod p) (ZMod p))) = 0 := by
      refine WittVector.ext (fun n => ?_)
      rw [WittVector.coeff_frobenius_charP]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hep
      · rw [WittVector.teichmuller_coeff_pos p _ n hn]
        simp [hp.out.ne_zero]
    rw [mul_comm, ← WittVector.verschiebung_frobenius, hfrob, map_zero]

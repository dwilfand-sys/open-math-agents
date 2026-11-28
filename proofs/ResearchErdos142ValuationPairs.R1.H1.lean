import OMAReductions.R_ResearchErdos142ValuationPairs_R1
import Mathlib

/-! Codex for dwilfand-sys. Each congruent ordered pair is determined by
two block numbers and one common residue. Subtract adjacent powers to count
the exact valuation shell in a prime-power interval. -/
namespace ValuationPairs
open OMA.R_ResearchErdos142ValuationPairs_R1

private noncomputable def decode (K D : ℕ) :
    ↥(pairs (K*D) D) ≃ Fin K × Fin K × Fin D where
  toFun z := ((finProdFinEquiv.symm z.val.1).1,
    (finProdFinEquiv.symm z.val.2).1,(finProdFinEquiv.symm z.val.1).2)
  invFun t := ⟨(finProdFinEquiv (t.1,t.2.2),finProdFinEquiv (t.2.1,t.2.2)), by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (t.2.2.val+D*t.1.val)%D=(t.2.2.val+D*t.2.1.val)%D
    simp⟩
  left_inv z := by
    have hr : (finProdFinEquiv.symm z.val.1).2=(finProdFinEquiv.symm z.val.2).2 :=
      Fin.ext (Finset.mem_filter.mp z.property).2
    apply Subtype.ext
    apply Prod.ext
    · exact finProdFinEquiv.apply_symm_apply _
    · change finProdFinEquiv ((finProdFinEquiv.symm z.val.2).1,
        (finProdFinEquiv.symm z.val.1).2) = z.val.2
      rw [hr]
      exact finProdFinEquiv.apply_symm_apply _
  right_inv t := by simp

private theorem count (K D : ℕ) : (pairs (K*D) D).card=K^2*D := by
  have h := Fintype.card_congr (decode K D)
  simpa [sq,mul_assoc] using h

private theorem divCount (n D : ℕ) (h : D∣n) : (pairs n D).card*D=n^2 := by
  obtain ⟨K,rfl⟩ := h
  rw [Nat.mul_comm D K,count]
  ring

private theorem exactCount (p e n : ℕ) (hp : 0<p) (hn : p^(e+1)∣n) :
    (shell n p e).card*p^(e+1)=n^2*(p-1) := by
  have div : p^e∣p^(e+1) := ⟨p,pow_succ ..⟩
  have sub : pairs n (p^(e+1)) ⊆ pairs n (p^e) := by
    intro z hz
    have h := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Nat.mod_mod_of_dvd z.1.val div).symm.trans
        ((congrArg (fun a => a%(p^e)) h).trans (Nat.mod_mod_of_dvd z.2.val div))⟩
  have part := Finset.card_sdiff_add_card_eq_card sub
  change (shell n p e).card+(pairs n (p^(e+1))).card=(pairs n (p^e)).card at part
  have cLow := divCount n (p^e) (div.trans hn)
  have cHigh := divCount n (p^(e+1)) hn
  have sum : (shell n p e).card*p^(e+1)+n^2=n^2*p := by
    calc
      _ = ((shell n p e).card+(pairs n (p^(e+1))).card)*p^(e+1) := by rw [Nat.add_mul,cHigh]
      _ = (pairs n (p^e)).card*(p^e*p) := by rw [part,pow_succ]
      _ = n^2*p := by rw [←Nat.mul_assoc,cLow]
  have pForm : p=(p-1)+1 := by omega
  have eq : n^2*p=n^2*(p-1)+n^2 := by
    conv_lhs => rw [pForm,Nat.mul_add,Nat.mul_one]
  omega

theorem complete : H1 := by
  refine ⟨count,exactCount,?_⟩
  intro p e L q hp hL
  have cL := exactCount p e L hp hL
  have cN := exactCount p e (q*L) hp (dvd_mul_of_dvd_right hL q)
  have power : 0<p^(e+1) := pow_pos hp _
  apply Nat.eq_of_mul_eq_mul_right power
  calc
    _ = (q*L)^2*(p-1) := cN
    _ = q^2*((shell L p e).card*p^(e+1)) := by rw [cL]; ring
    _ = _ := by ring

end ValuationPairs

theorem OMA.solution : OMA.R_ResearchErdos142ValuationPairs_R1.H1 := ValuationPairs.complete

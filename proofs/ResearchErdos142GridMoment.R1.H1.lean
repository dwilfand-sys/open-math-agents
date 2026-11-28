import OMAReductions.R_ResearchErdos142GridMoment_R1
import Mathlib

/-! Codex for dwilfand-sys. All quantities in the residual moment identity
are integer sums over actual finite data. No probability limits are used. -/
namespace GridMoment
open OMA.R_ResearchErdos142GridMoment_R1

set_option maxHeartbeats 4000000 in
private theorem sharp (q r k N C u v : ℕ) (hq : 2 ≤ q) (hsq : r*r ≤ q)
    (hu : 0<u) (hv : 0<v) (w : Fin N → ℕ) (W : Fin C → ℕ)
    (X : Fin u → Fin v → ℕ) (mass : total w=(k:ℤ)*q+r) (cosetMass : total W=total w)
    (small : ∀c, W c ≤ r) (bounds : ∀i j, k ≤ X i j ∧ X i j ≤ k+r)
    (row : ∀i, (q:ℤ)*total (X i)=(v:ℤ)*total w)
    (moment : (q:ℤ)^2*energy X=(u:ℤ)*v*((total w)^2+(q:ℤ)*squares w-squares W))
    (slide : (∀x, w x ≤ 1) → ∀(i : Fin u) (j l : Fin v), l.val=j.val+1 →
       X i j ≤ X i l+1 ∧ X i l ≤ X i j+1) : k=0 := by
  classical
  by_contra nonzero
  have hk : 1 ≤ k := by omega
  have q2 : (2:ℤ) ≤ q := by exact_mod_cast hq
  have qpos : 0<(q:ℤ) := by omega
  have rk : (r:ℤ)*(r:ℤ) ≤ q := by exact_mod_cast hsq
  have k1 : (1:ℤ) ≤ k := by exact_mod_cast hk
  have uv : 0<(u:ℤ)*v := by positivity
  have vpos : 0<(v:ℤ) := by positivity
  have rq : (r:ℤ)<q := by
    by_cases h : r ≤ 1
    · omega
    · have zur : (1:ℤ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      have z := mul_nonneg (sub_nonneg.mpr zur) (show (0:ℤ) ≤ r by positivity)
      by_contra hz
      push Not at hz
      have rr : (2:ℤ) ≤ r := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr rr) (show (0:ℤ) ≤ r by positivity)]
  let siteSlack (x : Fin N) : ℤ := (w x:ℤ)^2-w x
  have site_nn (x : Fin N) : 0 ≤ siteSlack x := by
    dsimp [siteSlack]
    by_cases h : w x=0
    · simp [h]
    · have z : (1:ℤ) ≤ w x := by exact_mod_cast (show 1 ≤ w x by omega)
      nlinarith [mul_nonneg (show 0 ≤ (w x:ℤ) by positivity) (sub_nonneg.mpr z)]
  have ss : 0 ≤ squares w-total w := by
    unfold squares total; rw [←Finset.sum_sub_distrib]; exact Finset.sum_nonneg (fun i _ => site_nn i)
  have cs : 0 ≤ (r:ℤ)*total w-squares W := by
    rw [←cosetMass]; unfold squares total; rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i _
    have h : (W i:ℤ) ≤ r := by exact_mod_cast small i
    nlinarith [mul_nonneg (show 0 ≤ (W i:ℤ) by positivity) (sub_nonneg.mpr h)]
  let loss (i : Fin u) (j : Fin v) : ℤ :=
    ((X i j:ℤ)-k)*((k:ℤ)+r-X i j)
  have loss_nn (i : Fin u) (j : Fin v) : 0 ≤ loss i j := by
    have lo : (k:ℤ) ≤ X i j := by exact_mod_cast (bounds i j).1
    have hi : (X i j:ℤ) ≤ (k:ℤ)+r := by exact_mod_cast (bounds i j).2
    exact mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi)
  let S : ℤ := ∑ i, ∑ j, loss i j
  have Snn : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => loss_nn i j))
  have rowLoss (i : Fin u) : (∑ j, loss i j) =
      -squares (X i) + (2*(k:ℤ)+r)*total (X i) -(v:ℤ)*(k*((k:ℤ)+r)) := by
    calc
      _ = ∑ j : Fin v, (-((X i j:ℤ)^2)+(2*(k:ℤ)+r)*(X i j:ℤ)-(k:ℤ)*(k+r)) := by
        apply Finset.sum_congr rfl; intro j _; dsimp [loss]; ring
      _ = _ := by simp [squares,total,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        Finset.sum_neg_distrib,←Finset.mul_sum]
  have whole : S = -energy X+(2*(k:ℤ)+r)*(∑ i, total (X i))-
      (u:ℤ)*v*((k:ℤ)*(k+r)) := by
    dsimp [S]
    simp_rw [rowLoss]
    simp [energy,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      Finset.sum_neg_distrib,←Finset.mul_sum,mul_assoc]
  have rows : (q:ℤ)*(∑ i, total (X i)) = (u:ℤ)*v*total w := by
    rw [Finset.mul_sum]
    simp_rw [row]
    simp [mul_assoc]
  have mainEq : (q:ℤ)^2*S = (u:ℤ)*v * (((k:ℤ)*q+r)^2*(-1) +
       q*(2*k+r)*((k:ℤ)*q+r)-(q:ℤ)^2*k*(k+r) - q*squares w + squares W) := by
    rw [whole]
    linear_combination -moment + ((q:ℤ)*(2*k+r))*rows -
      ((u:ℤ)*v*(total w+((k:ℤ)*q+r)))*mass +
      ((u:ℤ)*v*q*(2*k+r))*mass
  have Dnn : 0 ≤ (q:ℤ)*q*S := mul_nonneg (mul_nonneg qpos.le qpos.le) Snn
  have aNN := mul_nonneg qpos.le ss
  have nonnegLoss : 0 ≤ (q:ℤ)*(r*r-q) - q*(k-1)*(q-r) := by
    apply nonneg_of_mul_nonneg_right (a := (u:ℤ)*v) _ uv
    have extra := mul_nonneg uv.le (add_nonneg aNN cs)
    rw [mass] at extra
    nlinarith only [mainEq,Dnn,extra]
  have kex : 0 ≤ (q:ℤ)*(k-1)*(q-r) :=
    mul_nonneg (mul_nonneg qpos.le (by omega)) (by omega)
  have rex : 0 ≤ (q:ℤ)*(q-r*r) := mul_nonneg qpos.le (sub_nonneg.mpr rk)
  have kz : (q:ℤ)*(k-1)*(q-r)=0 := by nlinarith only [nonnegLoss,kex,rex]
  have rz : (q:ℤ)*(q-r*r)=0 := by nlinarith only [nonnegLoss,kex,rex]
  have rrEq : (q:ℤ)=(r:ℤ)*r := by
    rcases mul_eq_zero.mp rz with h|h <;> omega
  have kEq : (k:ℤ)=1 := by
    rcases mul_eq_zero.mp kz with h|h
    · rcases mul_eq_zero.mp h with h|h <;> omega
    · omega
  have R2 : (2:ℤ) ≤ r := by
    by_contra h
    have zerOr : r=0 ∨ r=1 := by omega
    rcases zerOr with h|h <;> simp [h] at rrEq <;> omega
  have balance : (q:ℤ)^2*S+(u:ℤ)*v*(q*(squares w-total w)+((r:ℤ)*total w-squares W))=0 := by
    rw [mass]
    linear_combination mainEq - ((u:ℤ)*v)*rz - ((u:ℤ)*v)*kz
  have sZero : S=0 := by
    have plus := mul_nonneg uv.le (add_nonneg aNN cs)
    have prod : (q:ℤ)^2*S=0 := by nlinarith only [balance,plus,Dnn]
    rcases mul_eq_zero.mp prod with h|h
    · nlinarith
    · exact h
  have siteZero : squares w-total w=0 := by
    have prod : (u:ℤ)*v*(q*(squares w-total w)+((r:ℤ)*total w-squares W))=0 := by
      rw [sZero] at balance; simpa using balance
    have h := (mul_eq_zero.mp prod).resolve_left (ne_of_gt uv)
    have zq : (q:ℤ)*(squares w-total w)=0 := by omega
    exact (mul_eq_zero.mp zq).resolve_left (ne_of_gt qpos)
  have binary : ∀x, w x ≤ 1 := by
    intro x
    have le := Finset.single_le_sum (f:=siteSlack) (fun i _ => site_nn i) (Finset.mem_univ x)
    have sum : (∑ i, siteSlack i)=squares w-total w := by simp [siteSlack,squares,total,Finset.sum_sub_distrib]
    rw [sum,siteZero] at le
    dsimp [siteSlack] at le
    by_contra no
    have big : (2:ℤ) ≤ w x := by exact_mod_cast (show 2 ≤ w x by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr big) (show 0 ≤ (w x:ℤ) by positivity)]
  have endpoints (i : Fin u) (j : Fin v) : X i j=k ∨ X i j=k+r := by
    have a := Finset.single_le_sum (f:=loss i) (fun z _ => loss_nn i z) (Finset.mem_univ j)
    have b := Finset.single_le_sum (f:=fun i => ∑ z,loss i z)
      (fun i _ => Finset.sum_nonneg (fun z _ => loss_nn i z)) (Finset.mem_univ i)
    have this : loss i j  ≤  S := le_trans a b
    have z : loss i j=0 := by omega
    rcases mul_eq_zero.mp z with h|h <;> omega
  let i : Fin u := ⟨0,hu⟩
  have constant (j : ℕ) (hj : j<v) : X i ⟨j,hj⟩ = X i ⟨0,hv⟩ := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj' : j<v := by omega
      have step := slide binary i ⟨j,hj'⟩ ⟨j+1,hj⟩ rfl
      have e1 := endpoints i ⟨j,hj'⟩
      have e2 := endpoints i ⟨j+1,hj⟩
      have neighborEq : X i ⟨j+1,hj⟩=X i ⟨j,hj'⟩ := by rcases e1 with h|h <;> rcases e2 with g|g <;> omega
      exact neighborEq.trans (ih hj')
  have tc : total (X i) = (v:ℤ)*X i ⟨0,hv⟩ := by
    unfold total
    simp_rw [show ∀ j : Fin v, (X i j:ℤ)=(X i ⟨0,hv⟩:ℤ) from fun j => by exact_mod_cast constant j.val j.isLt]
    simp
  have literal : (q:ℤ)*X i ⟨0,hv⟩=total w := by
    have z := row i
    rw [tc] at z
    exact mul_left_cancel₀ (ne_of_gt vpos) (by linear_combination z)
  have last := endpoints i ⟨0,hv⟩
  rcases last with h|h
  · rw [h,mass] at literal
    omega
  · rw [h,mass,Nat.cast_add] at literal
    nlinarith [mul_nonneg (show 0 ≤ (q:ℤ)-2 by omega) (show 0 ≤ (r:ℤ) by omega)]

theorem verified : H1 := sharp
end GridMoment

theorem OMA.solution : OMA.R_ResearchErdos142GridMoment_R1.H1 := GridMoment.verified

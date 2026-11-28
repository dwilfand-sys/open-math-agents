import OMAReductions.R_ResearchErdos142WeightedSecond_R1
import Mathlib

/-! Codex for dwilfand-sys. Expanding the finite square and interchanging
the sums transports the two-point incidence data to arbitrary integer weights. -/
namespace WeightedSecond
open OMA.R_ResearchErdos142WeightedSecond_R1

private theorem interchange {α β : Type*} [Fintype α] [Fintype β]
    (g : α → β → ℤ) : (∑ a, ∑ b, g a b) = ∑ b, ∑ a, g a b :=
  Finset.sum_comm

private theorem squareSum {C B : ℕ} (w : Fin C → Fin B → ℤ) :
    (∑ c, ∑ b, w c b)^2 = ∑ c, ∑ b, ∑ d, ∑ e, w c b * w d e := by
  simp only [sq,Finset.sum_mul,Finset.mul_sum]

private theorem base {C B : ℕ} (q : ℕ) (w : Fin C → Fin B → ℤ) :
    (∑ c, ∑ b, ∑ d, ∑ e, (if c≠d then (1:ℤ) else if b=e then q else 0)*w c b*w d e) =
    (mass w)^2 + q*sitesSq w-classesSq w := by
  classical
  let a (c : Fin C) (b : Fin B) (d : Fin C) (e : Fin B) := w c b*w d e
  have adjust (c b d e) : (if c≠d then (1:ℤ) else if b=e then q else 0)*w c b*w d e =
      a c b d e - (if d=c then a c b d e else 0) +
      (if d=c then if e=b then (q:ℤ)*w c b^2 else 0 else 0) := by
    dsimp [a]
    by_cases cd : c=d <;> by_cases be : b=e <;> simp_all <;> ring
  have all : (∑ c, ∑ b, ∑ d, ∑ e, a c b d e)=(mass w)^2 :=
    (squareSum w).symm
  have within : (∑ c, ∑ b, ∑ d, ∑ e, if d=c then a c b d e else 0) = classesSq w := by
    simp only [←Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    unfold classesSq
    simp only [a,sq,Finset.sum_mul,Finset.mul_sum]
  have diagonal : (∑ c, ∑ b, ∑ d, ∑ e, if d=c then if e=b then (q:ℤ)*w c b^2 else 0 else 0) =
      (q:ℤ)*sitesSq w := by
    simp [sitesSq,Finset.mul_sum]
  simp_rw [adjust]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [all,within,diagonal]
  ring

theorem transfer : H1 := by
  classical
  intro R C B q I pairs w
  let f (j : Fin R) (c : Fin C) (b : Fin B) (d : Fin C) (e : Fin B) :=
    (q:ℤ)^2 * ((I j c b * w c b) * (I j d e * w d e))
  have expand (j : Fin R) : (q:ℤ)^2*(weight I w j)^2 = ∑ c,∑ b,∑ d,∑ e, f j c b d e := by
    unfold weight
    rw [squareSum]
    simp only [Finset.mul_sum,f]
  have move : (∑ j,∑ c,∑ b,∑ d,∑ e,f j c b d e) =
      ∑ c,∑ b,∑ d,∑ e,∑ j,f j c b d e := by
    rw [interchange (fun j c => ∑ b,∑ d,∑ e,f j c b d e)]
    apply Finset.sum_congr rfl
    intro c _
    rw [interchange (fun j b => ∑ d,∑ e,f j c b d e)]
    apply Finset.sum_congr rfl
    intro b _
    rw [interchange (fun j d => ∑ e,f j c b d e)]
    apply Finset.sum_congr rfl
    intro d _
    exact interchange (fun j e => f j c b d e)
  have evaluate (c b d e) : (∑ j, f j c b d e) =
      (R:ℤ)*((if c≠d then (1:ℤ) else if b=e then q else 0)*w c b*w d e) := by
    calc
      _ = ∑ j, ((q:ℤ)^2*(I j c b*I j d e))*w c b*w d e := by
        apply Finset.sum_congr rfl; intro j _; dsimp [f]; ring
      _ = _ := by rw [←Finset.sum_mul,←Finset.sum_mul,←Finset.mul_sum,pairs]; ring
  calc
    _ = ∑ j, (q:ℤ)^2*(weight I w j)^2 := Finset.mul_sum ..
    _ = ∑ j, ∑ c,∑ b,∑ d,∑ e,f j c b d e := by simp_rw [expand]
    _ = _ := by rw [move]; simp_rw [evaluate]; simpa only [←Finset.mul_sum] using congrArg (fun z : ℤ => (R:ℤ)*z) (base q w)

end WeightedSecond

theorem OMA.solution : OMA.R_ResearchErdos142WeightedSecond_R1.H1 := WeightedSecond.transfer

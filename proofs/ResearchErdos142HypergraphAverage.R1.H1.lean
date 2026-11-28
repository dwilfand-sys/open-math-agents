import OMAReductions.R_ResearchErdos142HypergraphAverage_R1
import Mathlib

/-! Codex for dwilfand-sys. This formalizes classical alteration and
incidence double counting for the prime-cyclic route suggested by @eilamc14. -/
namespace HypergraphAverage
open OMA.R_ResearchErdos142HypergraphAverage_R1

private theorem alteration {α : Type} [DecidableEq α] (V : Finset α)
    (E : Finset (Finset α)) (R : ℕ) (nonempty : ∀ e∈E, e.Nonempty)
    (indep : ∀ B⊆V, (∀ e∈E, ¬e⊆B) → B.card≤R)
    (T : Finset α) (sub : T⊆V) :
    T.card-R ≤ (E.filter (fun e => e ⊆ T)).card := by
  classical
  let F := E.filter (fun e => e ⊆ T)
  let choose (e : ↥F) : α :=
    Classical.choose (nonempty e.val (Finset.mem_filter.mp e.property).1)
  have hit (e : ↥F) : choose e ∈ e.val :=
    Classical.choose_spec (nonempty e.val (Finset.mem_filter.mp e.property).1)
  let H := (Finset.univ : Finset ↥F).image choose
  have hc : H.card ≤ F.card := by
    simpa [H] using (Finset.card_image_le (s := (Finset.univ : Finset ↥F)) (f := choose))
  have independent : ∀ e∈E, ¬e⊆T \ H := by
    intro e he bad
    have et : e⊆T := fun x hx => (Finset.mem_sdiff.mp (bad hx)).1
    let fe : ↥F := ⟨e,Finset.mem_filter.mpr ⟨he,et⟩⟩
    have gone : choose fe ∈ H := Finset.mem_image.mpr ⟨fe,Finset.mem_univ _,rfl⟩
    exact (Finset.mem_sdiff.mp (bad (hit fe))).2 gone
  have ir := indep (T \ H) (fun x hx => sub (Finset.mem_sdiff.mp hx).1) independent
  have loss := Finset.le_card_sdiff H T
  change T.card-R ≤ F.card
  omega

theorem supersaturation : H1 := by
  classical
  intro α V E k t R hk kt _ uniform independent
  let Ts := V.powersetCard t
  have ne (e : Finset α) (he : e∈E) : e.Nonempty :=
    Finset.card_pos.mp (by rw [(uniform e he).2]; exact hk)
  have small (T : Finset α) (hT : T∈Ts) :
      t-R ≤ (E.filter (fun e => e ⊆ T)).card := by
    obtain ⟨sub,card⟩ := Finset.mem_powersetCard.mp hT
    simpa [card] using alteration V E R ne independent T sub
  have codeg (e : Finset α) (he : e∈E) :
      (Ts.filter (fun T => e⊆T)).card=(V.card-k).choose (t-k) := by
    rw [Finset.card_filter_powersetCard_subset e V t (uniform e he).1 (by rw [(uniform e he).2]; exact kt),
      (uniform e he).2]
  calc
    _ = ∑ _T ∈ Ts, (t-R) := by simp [Ts,Finset.card_powersetCard,Nat.mul_comm]
    _ ≤ ∑ T ∈ Ts,(E.filter (fun e => e ⊆ T)).card := Finset.sum_le_sum small
    _ = ∑ T ∈ Ts,∑ e ∈ E, if e⊆T then 1 else 0 := by simp
    _ = ∑ e ∈ E,∑ T ∈ Ts, if e⊆T then 1 else 0 := Finset.sum_comm
    _ = ∑ e ∈ E,(Ts.filter (fun T => e ⊆ T)).card := by simp
    _ = ∑ _e ∈ E,(V.card-k).choose (t-k) := Finset.sum_congr rfl codeg
    _ = _ := by simp

end HypergraphAverage

theorem OMA.solution : OMA.R_ResearchErdos142HypergraphAverage_R1.H1 :=
  HypergraphAverage.supersaturation

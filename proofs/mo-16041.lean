import OMAStatements.S_mo_16041
import Mathlib

/-!
# Equal sums in bounded multisets

Credit: @dwilfand-sys (formalization by Codex). Zeyu posed the general
question on MathOverflow. Gjergji Zaimi identified 1993 Putnam A4 there.
The classical prefix-sum proof is given in the Kalva archive for arbitrary
lengths. Claude Code independently supplied that strategy for this target.
Source: https://prase.cz/kalva/putnam/psoln/psol934.html
-/

namespace MO16041

private noncomputable def prefixPart (S : Multiset ℕ) (i : ℕ) : Multiset ℕ :=
  S.toList.take i

private theorem prefix_last (S : Multiset ℕ) : prefixPart S S.card = S := by
  unfold prefixPart
  rw [← Multiset.length_toList S, List.take_length, Multiset.coe_toList]

private theorem prefix_step (S : Multiset ℕ) {i : ℕ} (hi : i < S.card) :
    ∃ v ∈ S, prefixPart S (i+1) = prefixPart S i + {v} := by
  have h : i < S.toList.length := by simpa using hi
  refine ⟨S.toList[i], Multiset.mem_toList.mp (List.getElem_mem h), ?_⟩
  unfold prefixPart
  rw [List.take_succ_eq_append_getElem h] <;> rfl

private theorem prefix_mono (S : Multiset ℕ) : Monotone (prefixPart S) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < S.card
  · obtain ⟨v,_,h⟩ := prefix_step S hi
    rw [h]
    exact Multiset.le_add_right _ _
  · have h : S.toList.length ≤ i := by simpa using (Nat.le_of_not_gt hi)
    simp [prefixPart, List.take_of_length_le h, List.take_of_length_le (h.trans (Nat.le_succ _))]

private theorem sum_mono (S : Multiset ℕ) {i j : ℕ} (hij : i ≤ j) :
    (prefixPart S i).sum ≤ (prefixPart S j).sum := by
  obtain ⟨v,h⟩ := Multiset.le_iff_exists_add.mp (prefix_mono S hij)
  rw [h, Multiset.sum_add]
  omega

private theorem sum_strict (S : Multiset ℕ) (hS : ∀ a ∈ S, 0 < a)
    {i j : ℕ} (hij : i < j) (hj : j ≤ S.card) :
    (prefixPart S i).sum < (prefixPart S j).sum := by
  obtain ⟨v,hv,he⟩ := prefix_step S (show i < S.card by omega)
  have h := sum_mono S (show i+1 ≤ j by omega)
  rw [he, Multiset.sum_add, Multiset.sum_singleton] at h
  have := hS v hv
  omega

private theorem next_cut (S : Multiset ℕ) (c b : ℕ) (hb : 0 < b)
    (hS : ∀ v ∈ S, v ≤ b) (hc : c ≤ S.sum) :
    ∃ j ≤ S.card, c ≤ (prefixPart S j).sum ∧ (prefixPart S j).sum < c + b := by
  classical
  have hlast : c ≤ (prefixPart S S.card).sum := by simpa only [prefix_last] using hc
  have existsCut : ∃ j, c ≤ (prefixPart S j).sum := ⟨S.card,hlast⟩
  let j := Nat.find existsCut
  have hj : j ≤ S.card := Nat.find_min' existsCut hlast
  refine ⟨j,hj,Nat.find_spec existsCut,?_⟩
  cases he : j with
  | zero => simpa [prefixPart] using (show 0 < c+b by omega)
  | succ k =>
    have hk : k < j := by omega
    have hbefore : ¬c ≤ (prefixPart S k).sum := Nat.find_min existsCut hk
    obtain ⟨v,hv,hstep⟩ := prefix_step S (show k < S.card by omega)
    rw [hstep, Multiset.sum_add, Multiset.sum_singleton]
    have := hS v hv
    omega

private def matched (S T : Multiset ℕ) : Prop :=
  ∃ X ≤ S, ∃ Y ≤ T, X ≠ 0 ∧ Y ≠ 0 ∧ X.sum = Y.sum

private theorem ordered (S T : Multiset ℕ) (hcard : 0 < S.card)
    (hS : ∀ a ∈ S, 0 < a) (hT : ∀ b ∈ T, b ≤ S.card) (horder : S.sum ≤ T.sum) :
    matched S T := by
  classical
  have cuts (i : Fin (S.card+1)) : ∃ j ≤ T.card,
      (prefixPart S i.val).sum ≤ (prefixPart T j).sum ∧
      (prefixPart T j).sum < (prefixPart S i.val).sum + S.card := by
    apply next_cut T _ _ hcard hT
    have hi : i.val ≤ S.card := by have := i.isLt; omega
    have bound : (prefixPart S i.val).sum ≤ S.sum := by
      simpa only [prefix_last] using sum_mono S hi
    exact bound.trans horder
  choose j hj using cuts
  let f (i : Fin (S.card+1)) : Fin S.card :=
    ⟨(prefixPart T (j i)).sum - (prefixPart S i.val).sum, by
      have hlow := (hj i).2.1
      have hhigh := (hj i).2.2
      omega⟩
  obtain ⟨i,k,hne,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have extract (a b : Fin (S.card+1)) (hab : a < b) (habf : f a = f b) :
      matched S T := by
    have hlt : a.val < b.val := hab
    have hb : b.val ≤ S.card := by have := b.isLt; omega
    have haSum := sum_strict S hS hlt hb
    have he := congrArg Fin.val habf
    change (prefixPart T (j a)).sum - (prefixPart S a.val).sum =
      (prefixPart T (j b)).sum - (prefixPart S b.val).sum at he
    have hga := (hj a).2.1
    have hgb := (hj b).2.1
    have hjab : j a ≤ j b := by
      by_contra! hj'
      have back := sum_mono T hj'.le
      omega
    let X := prefixPart S b.val - prefixPart S a.val
    let Y := prefixPart T (j b) - prefixPart T (j a)
    have hX : X + prefixPart S a.val = prefixPart S b.val :=
      Multiset.sub_add_cancel (prefix_mono S hlt.le)
    have hY : Y + prefixPart T (j a) = prefixPart T (j b) :=
      Multiset.sub_add_cancel (prefix_mono T hjab)
    have hx := congrArg Multiset.sum hX
    have hy := congrArg Multiset.sum hY
    rw [Multiset.sum_add] at hx hy
    have hXle : X ≤ S := (Multiset.sub_le_self _ _).trans
      (by simpa only [prefix_last] using prefix_mono S hb)
    have hYle : Y ≤ T := (Multiset.sub_le_self _ _).trans
      (by simpa only [prefix_last] using prefix_mono T (hj b).1)
    refine ⟨X,hXle,Y,hYle,?_,?_,by omega⟩
    · intro h0
      rw [h0,Multiset.sum_zero] at hx
      omega
    · intro h0
      rw [h0,Multiset.sum_zero] at hy
      omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact extract i k h heq
  · exact extract k i h heq.symm

private theorem solve : type_of% @OMA.S_mo_16041.main := by
  intro n m hn hm A B hA hB ha hb
  subst n
  subst m
  rcases le_total A.sum B.sum with h | h
  · exact ordered A B hn (fun a h => (ha a h).1) (fun b h => (hb b h).2) h
  · obtain ⟨Y,hY,X,hX,hY0,hX0,hEq⟩ :=
      ordered B A hm (fun b h => (hb b h).1) (fun a h => (ha a h).2) h
    exact ⟨X,hX,Y,hY,hX0,hY0,hEq.symm⟩

end MO16041

theorem OMA.solution : type_of% @OMA.S_mo_16041.main := MO16041.solve

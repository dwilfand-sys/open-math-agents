import OMAReductions.R_ResearchErdos142ShearMajority_R1
import Mathlib

/-! Codex for dwilfand-sys. Linear shears over a prime-power quotient and
sliding equal-width partitions turn the general column lemma into a full
coset whenever two low residue classes occur. -/
namespace ShearMajority
open OMA.R_ResearchErdos142ShearMajority_R1

private theorem bin_shear (q L o j x : ℕ) (hL : 0 < L) :
    bin q L o (1+j*L) x = ((o+x)/L+j*x)%q := by
  unfold bin
  rw [show o+(1+j*L)*x = (o+x)+L*(j*x) by ring, Nat.add_mul_div_left _ _ hL]

private theorem slopeUnit {p t x y : ℕ} (hp : p.Prime) (ht : 0<t)
    (le : y≤x) (ne : x%p≠y%p) : IsUnit ((x : ZMod (p^t)) - y) := by
  rw [← Nat.cast_sub le, ZMod.isUnit_natCast_iff_not_dvd_pow hp ht]
  intro h
  have dz := Nat.mod_eq_zero_of_dvd h
  apply ne
  calc
    x%p = ((x-y)+y)%p := by rw [Nat.sub_add_cancel le]
    _ = y%p := by rw [Nat.add_mod, dz, Nat.zero_add, Nat.mod_mod]

private theorem linearMeet {p t : ℕ} (hp : p.Prime) (ht : 0<t)
    (A B x y : ℕ) (ne : x%p ≠ y%p) :
    ∃ j : Fin (p^t), (A+j.val*x)%(p^t) = (B+j.val*y)%(p^t) := by
  letI : NeZero (p^t) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have unit : IsUnit ((x : ZMod (p^t)) - y) := by
    rcases le_total y x with h|h
    · exact slopeUnit hp ht h ne
    · have z := (slopeUnit hp ht h (Ne.symm ne)).neg
      simpa using z
  obtain ⟨u,hu⟩ := unit
  let J : ZMod (p^t) := ((B : ZMod (p^t))-A)*↑(u⁻¹)
  have prod : J*((x : ZMod (p^t))-y) = (B : ZMod (p^t))-A := by
    rw [←hu]
    simp [J,mul_assoc]
  have eq : (A : ZMod (p^t))+J*x = B+J*y := by linear_combination prod
  refine ⟨⟨J.val,J.val_lt⟩,(ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_⟩
  simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] using eq

private theorem thresholdBin (q L r x : ℕ) (hL : 0<L) (hr : r≤L) :
    bin q L (L-r) 1 x = (x/L+(if r≤x%L then 1 else 0))%q := by
  unfold bin
  rw [one_mul, show L-r+x=(L-r+x%L)+L*(x/L) by
    have d := Nat.mod_add_div x L; omega, Nat.add_mul_div_left _ _ hL]
  have rem := Nat.mod_lt x hL
  by_cases h : r ≤ x%L
  · rw [if_pos h, show L-r+x%L=(x%L-r)+L*1 by omega, Nat.add_mul_div_left _ _ hL,
      Nat.div_eq_of_lt (show x%L-r<L by omega)]
    simp [Nat.add_comm]
  · rw [if_neg h, Nat.div_eq_of_lt (show L-r+x%L<L by omega)]
    simp

private theorem geometric {q L : ℕ} (hq : 2≤q) (hL : 0<L)
    (pos : Fin (q+1) → Fin (q*L)) (a : Fin (q+1))
    (hinj : ∀ o i k, i≠a → k≠a → bin q L o 1 (pos i).val =
       bin q L o 1 (pos k).val → i=k) :
    ∃ r : ℕ, r<L ∧ (∀ i, i≠a → (pos i).val%L=r) ∧
      ∀ b : Fin q, ∃ i, i≠a ∧ (pos i).val=b.val*L+r := by
  classical
  let B (i : Fin (q+1)) : Fin q := ⟨bin q L 0 1 (pos i).val,Nat.mod_lt _ (by omega)⟩
  let S := (Finset.univ : Finset (Fin (q+1))).erase a
  have sc : S.card=q := by simp [S, Finset.card_erase_of_mem]
  have bi : Set.InjOn B (S : Set (Fin (q+1))) := by
    intro i hi k hk h
    exact hinj 0 i k (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hk).1 (congrArg Fin.val h)
  have im : S.image B=Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ _) (by rw [Finset.card_image_of_injOn bi,sc]; simp)
  have sur (b : Fin q) : ∃ i, i≠a ∧ B i=b := by
    have mem : b ∈ S.image B := by rw [im]; simp
    obtain ⟨i,hi,h⟩ := Finset.mem_image.mp mem
    exact ⟨i,(Finset.mem_erase.mp hi).1,h⟩
  choose w wn wb using sur
  have wdiv (b : Fin q) : (pos (w b)).val/L=b.val := by
    have lt : (pos (w b)).val/L < q := (Nat.div_lt_iff_lt_mul hL).2 (pos (w b)).isLt
    simpa [B,bin,Nat.mod_eq_of_lt lt] using congrArg Fin.val (wb b)
  let r (b : Fin q) := (pos (w b)).val%L
  have step (b c : Fin q) (next : c.val=(b.val+1)%q) : r b ≤ r c := by
    by_contra hn
    have rle : r b≤L := (Nat.mod_lt _ hL).le
    have hc : ¬r b ≤ (pos (w c)).val%L := by change ¬r b ≤ r c; omega
    have he : bin q L (L-r b) 1 (pos (w b)).val = bin q L (L-r b) 1 (pos (w c)).val := by
      rw [thresholdBin _ _ _ _ hL rle, thresholdBin _ _ _ _ hL rle,
        if_pos (show r b ≤ (pos (w b)).val%L from le_rfl), if_neg hc,
        wdiv,wdiv,Nat.add_zero,Nat.mod_eq_of_lt c.isLt]
      exact next.symm
    have hw := hinj _ _ _ (wn b) (wn c) he
    have bc : b=c := (wb b).symm.trans ((congrArg B hw).trans (wb c))
    exact hn (by rw [bc])
  let atN (j : ℕ) : Fin q := ⟨j%q,Nat.mod_lt _ (by omega)⟩
  have mon : Monotone (fun j : ℕ => r (atN j)) := monotone_nat_of_le_succ (fun j =>
    step _ _ (by simp [atN,Nat.add_mod]))
  have endEq : atN q = atN 0 := Fin.ext (by simp [atN])
  have fixed (b : Fin q) : r b = r (atN 0) := by
    have bform : atN b.val=b := Fin.ext (Nat.mod_eq_of_lt b.isLt)
    have lo : r (atN 0) ≤ r (atN b.val) := mon (Nat.zero_le b.val)
    have hi : r (atN b.val) ≤ r (atN q) := mon b.isLt.le
    rw [bform] at lo hi
    rw [endEq] at hi
    omega
  refine ⟨r (atN 0),Nat.mod_lt _ hL,?_,?_⟩
  · intro i hi
    have eq : w (B i)=i := hinj 0 _ _ (wn _) hi (congrArg Fin.val (wb (B i)))
    simpa [r,eq] using fixed (B i)
  · intro b
    refine ⟨w b,wn b,?_⟩
    have dec := Nat.mod_add_div (pos (w b)).val L
    have rem : (pos (w b)).val%L=r (atN 0) := fixed b
    rw [rem,wdiv] at dec
    simpa [Nat.add_comm,Nat.mul_comm] using dec.symm

theorem shear_majority : H1 := by
  classical
  intro p t L hp ht hL pdL pos allBins
  let q := p^t
  have hq : 2≤q := by
    dsimp [q]
    cases t with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      have h := Nat.mul_le_mul_right p (show 1≤p^k from Nat.one_le_pow _ _ hp.pos)
      simpa using le_trans hp.two_le (by simpa using h)
  let color (i : Fin (q+1)) := (pos i).val%p
  let C (o : ℕ) (j : Fin q) (i : Fin (q+1)) : Fin q :=
    ⟨bin q L o (1+j.val*L) (pos i).val, Nat.mod_lt _ (by omega)⟩
  have sur (o : ℕ) (j : Fin q) : Function.Surjective (C o j) := by
    intro b
    have cL : Nat.Coprime (1+j.val*L) L := (Nat.coprime_add_mul_right_left 1 L j.val).2 (by simp)
    have cp : Nat.Coprime (1+j.val*L) p := cL.of_dvd_right pdL
    have ca : Nat.Coprime (1+j.val*L) (p^t*L) := Nat.coprime_mul_iff_right.mpr ⟨cp.pow_right t,cL⟩
    obtain ⟨i,hi⟩ := allBins _ ca o b
    exact ⟨i,Fin.ext hi⟩
  have meet (o : ℕ) (x y : Fin (q+1)) (ne : color x≠color y) :
      ∃ j, C o j x=C o j y := by
    obtain ⟨j,hj⟩ := linearMeet hp ht ((o+(pos x).val)/L) ((o+(pos y).val)/L)
      (pos x).val (pos y).val ne
    exact ⟨j,Fin.ext (by change bin q L o _ _ = bin q L o _ _;
      rw [bin_shear _ _ _ _ _ hL,bin_shear _ _ _ _ _ hL]; exact hj)⟩
  by_cases mono : ∀ i k, color i=color k
  · exact Or.inl mono
  right
  have split (o : ℕ) := ((ColumnPairs.count_and_classify q color (C o) (sur o) (meet o)).2.resolve_left mono).2
  obtain ⟨a,alone,_,_⟩ := split 0
  have stable (o : ℕ) : ∀ i k, i≠a → k≠a →
      bin q L o 1 (pos i).val = bin q L o 1 (pos k).val → i=k := by
    obtain ⟨b,_,other,one⟩ := split o
    have ab : a=b := by
      by_contra ne
      have existsThird : ∃ z : Fin (q+1), z≠a ∧ z≠b := by
        by_contra nope
        push Not at nope
        have sub : (Finset.univ : Finset (Fin (q+1))) ⊆ {a,b} := by
          intro z _
          by_cases eq : z=a
          · simp [eq]
          · simp [nope z eq]
        have lh := Finset.card_le_card sub
        simp [ne] at lh
        omega
      obtain ⟨z,za,zb⟩ := existsThird
      exact alone z za (other z a zb ne)
    subst b
    intro i k hi hk he
    let j : Fin q := ⟨0,by omega⟩
    apply one j i k hi hk
    apply Fin.ext
    simpa [C,j] using he
  obtain ⟨r,rl,ar,full⟩ := geometric hq hL pos a stable
  exact ⟨a,r,rl,alone,ar,full⟩

end ShearMajority

theorem OMA.solution : OMA.R_ResearchErdos142ShearMajority_R1.H1 := ShearMajority.shear_majority

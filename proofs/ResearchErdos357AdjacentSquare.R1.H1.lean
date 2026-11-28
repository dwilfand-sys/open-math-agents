import OMAReductions.R_ResearchErdos357AdjacentSquare_R1
import Mathlib.Tactic.Ring

/-! Codex for dwilfand-sys. A copied patch with gaps one or two gives two
actual contiguous windows. A literal adjacent square supplies the multiple
automatically by rounding the first positive site upward. -/
namespace AdjacentSquare
open OMA.R_ResearchErdos357AdjacentSquare_R1

private theorem ws (f : ℕ → ℕ) (i n : ℕ) :
    window f i (n+1) = window f i n + f (i+n) := by
  simp [window, Finset.sum_range_succ]

private theorem oneW (f : ℕ → ℕ) (i : ℕ) : window f i 1 = f i := by
  simp [window]

private theorem twoW (f : ℕ → ℕ) (i : ℕ) :
    window f i 2 = f i + f (i+1) := by
  rw [ws f i 1, oneW]

private theorem cut (f : ℕ → ℕ) (i a b : ℕ) :
    window f i (a+b) = window f i a + window f (i+a) b := by
  induction b with
  | zero => simp [window]
  | succ b ih =>
    calc
      window f i (a+(b+1)) = window f i (a+b) + f (i+(a+b)) := ws f i (a+b)
      _ = window f i a + window f (i+a) (b+1) := by rw [ih, ws]; simp [Nat.add_assoc]

private theorem translate (f : ℕ → ℕ) (N L D : ℕ) (hc : copy f N L D)
    (i b : ℕ) : i+b ≤ N+1 →
    window f (L+i) b = window f i b + b*D := by
  induction b with
  | zero => intro _; simp [window]
  | succ b ih =>
    intro h
    have hr := ih (by omega)
    have hf := hc (i+b) (by omega)
    rw [ws, ws, hr, show L+i+b=L+(i+b) by omega, hf, Nat.succ_mul]
    omega

private theorem anchor (f : ℕ → ℕ) (x : ℕ) (low : f 0 ≤ x) (N : ℕ) :
    smallGaps f N → x ≤ f N →
    ∃ b d : ℕ, (d = 1 ∨ d = 2) ∧ b+d ≤ N+1 ∧ window f b d = d*x := by
  induction N with
  | zero =>
    intro _ high
    have eq : f 0 = x := by omega
    exact ⟨0, 1, Or.inl rfl, by decide, by rw [oneW, eq, Nat.one_mul]⟩
  | succ N ih =>
    intro hg high
    by_cases prev : x ≤ f N
    · have smaller : smallGaps f N := fun i hi => hg i (by omega)
      obtain ⟨b,d,hd,limit,hb⟩ := ih smaller prev
      exact ⟨b,d,hd,by omega,hb⟩
    · by_cases eq : f (N+1) = x
      · exact ⟨N+1,1,Or.inl rfl,by omega,by rw [oneW,eq,Nat.one_mul]⟩
      · have gap := (hg N (by omega)).2
        exact ⟨N,2,Or.inr rfl,by omega,by rw [twoW]; omega⟩

private theorem general (f : ℕ → ℕ) (N L D t : ℕ) (hg : smallGaps f N)
    (hc : copy f N L D) (ht : 0 < t) (low : f 0 ≤ t*D) (high : t*D ≤ f N)
    (room : 4*t ≤ N) : collision f (L+N+1) t := by
  obtain ⟨b,d,hd,limit,hb⟩ := anchor f (t*D) low N hg high
  have hdpos : 0 < d := by rcases hd with h|h <;> omega
  have hdmax : d ≤ 2 := by rcases hd with h|h <;> omega
  have hpos := Nat.mul_pos hdpos ht
  have hmax := Nat.mul_le_mul_right t hdmax
  have pay : d*(t*D) = d*t*D := (Nat.mul_assoc d t D).symm
  by_cases left : d*t ≤ b
  · have back : b-d*t+d*t=b := by omega
    refine ⟨b-d*t,d*t+d,L+(b-d*t),d*t,hpos,by omega,by omega,by omega,by omega,?_⟩
    rw [cut, back, hb, translate f N L D hc (b-d*t) (d*t) (by omega), pay]
  · have right : b+d+d*t ≤ N+1 := by omega
    refine ⟨b,d+d*t,L+(b+d),d*t,hpos,by omega,by omega,by omega,by omega,?_⟩
    rw [cut, hb, translate f N L D hc (b+d) (d*t) right, pay, Nat.add_comm]

theorem verdict : H1 := by
  refine ⟨general, ?_⟩
  intro f N D hpos hD hg hc room
  have startEnd : f N = f 0 + D := by simpa using hc 0 (by omega)
  have mulEq : ((f 0-1)/D+1)*D = D*((f 0-1)/D)+D := by ring
  have remEq := Nat.mod_add_div (f 0-1) D
  have remLt := Nat.mod_lt (f 0-1) hD
  have low : f 0 ≤ ((f 0-1)/D+1)*D := by omega
  have high : ((f 0-1)/D+1)*D ≤ f N := by omega
  have result := general f N N D ((f 0-1)/D+1) hg hc (Nat.succ_pos _) low high room
  simpa [two_mul] using result

end AdjacentSquare

theorem OMA.solution : OMA.R_ResearchErdos357AdjacentSquare_R1.H1 := AdjacentSquare.verdict

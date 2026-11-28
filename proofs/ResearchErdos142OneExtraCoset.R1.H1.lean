import OMAReductions.R_ResearchErdos142OneExtraCoset_R1
import Mathlib

/-! Codex for dwilfand-sys. Single-residue descent, lifting of the coset,
and the converse for every prime-power period. -/
namespace OneExtraCoset
open OMA.R_ResearchErdos142OneExtraCoset_R1 OMA.R_ResearchErdos142ShearMajority_R1

private theorem downBin (p q L o u y r : ℕ) (hp : 0<p) (hq : 0<q) (hL : 0<L) :
    bin q (L*p) (p*o+(u*r)*(p*(q*L)-1)) u (p*y+r) = bin q L o u y := by
  have positive : 0 < p*(q*L) := Nat.mul_pos hp (Nat.mul_pos hq hL)
  have restore : p*(q*L)-1+1=p*(q*L) := by omega
  have eq : p*o+(u*r)*(p*(q*L)-1)+u*(p*y+r) =
      p*((o+u*y)+L*(q*(u*r))) := by
    calc
      _ = p*(o+u*y) + (u*r)*((p*(q*L)-1)+1) := by ring
      _ = _ := by rw [restore]; ring
  unfold bin
  rw [eq,Nat.mul_comm L p,Nat.mul_div_mul_left _ _ hp,Nat.add_mul_div_left _ _ hL,
    Nat.add_mul_mod_self_left]

private def down {q L p : ℕ} (hp : 0<p) (pos : Fin (q+1) → Fin (q*(L*p)))
    (i : Fin (q+1)) : Fin (q*L) :=
  ⟨(pos i).val/p,(Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_assoc] using (pos i).isLt)⟩

private theorem nextLevel {p q L : ℕ} (hp : 0<p) (hq : 0<q) (hL : 0<L)
    (pdiv : p∣q) (pos : Fin (q+1) → Fin (q*(L*p))) (hi : Function.Injective pos)
    (h : covered q (L*p) pos) (m : ∀i k, (pos i).val%p=(pos k).val%p) :
    ∃ r : ℕ, r<p ∧ (∀ i, (pos i).val=p*(down hp pos i).val+r) ∧
      Function.Injective (down hp pos) ∧ covered q L (down hp pos) := by
  let r := (pos 0).val%p
  have dec (i : Fin (q+1)) : (pos i).val = p*(down hp pos i).val+r := by
    have z := Nat.mod_add_div (pos i).val p
    rw [m i 0] at z
    simpa [r,down,Nat.add_comm] using z.symm
  refine ⟨r,Nat.mod_lt _ hp,dec,?_,?_⟩
  · intro i j eq
    apply hi
    apply Fin.ext
    rw [dec i,dec j,eq]
  · intro u cop o b
    have cp : u.Coprime p := cop.of_dvd_right (dvd_mul_of_dvd_left pdiv L)
    have cu : u.Coprime (q*(L*p)) := by
      rw [←Nat.mul_assoc]
      exact Nat.coprime_mul_iff_right.mpr ⟨cop,cp⟩
    obtain ⟨i,he⟩ := h u cu (p*o+(u*r)*(p*(q*L)-1)) b
    use i
    rw [dec i,downBin _ _ _ _ _ _ _ hp hq hL] at he
    exact he

private theorem forward (p t : ℕ) (hp : p.Prime) (ht : 0<t) (k : ℕ) :
    ∀ pos : Fin (p^t+1) → Fin (p^t*p^k), Function.Injective pos →
      covered (p^t) (p^k) pos → fullCoset (p^t) (p^k) pos := by
  induction k with
  | zero =>
    intro pos hi _
    have impossible := Fintype.card_le_of_injective pos hi
    simp at impossible
  | succ k ih =>
    simp only [pow_succ]
    intro pos hi cov
    have hq : 0<p^t := pow_pos hp.pos _
    have hL : 0<p^k := pow_pos hp.pos _
    have pdiv : p∣p^t := dvd_pow_self _ (by omega)
    have divL : p∣p^k*p := dvd_mul_left _ _
    rcases ShearMajority.shear_majority p t (p^k*p) hp ht (Nat.mul_pos hL hp.pos) divL pos cov with
      mono | ⟨a,r,rl,_,_,fill⟩
    · obtain ⟨r,hr,dec,di,dc⟩ := nextLevel hp.pos hq hL pdiv pos hi cov mono
      obtain ⟨s,hs,full⟩ := ih (down hp.pos pos) di dc
      have range : p*s+r < p^k*p := by
        have bound := Nat.mul_le_mul_left p (show s+1≤p^k by omega)
        rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm p (p^k)] at bound
        omega
      refine ⟨p*s+r,range,?_⟩
      intro b
      obtain ⟨i,hit⟩ := full b
      refine ⟨i,?_⟩
      rw [dec i,hit]
      ring
    · exact ⟨r,rl,fun b => by obtain ⟨i,_,ok⟩ := fill b; exact ⟨i,ok⟩⟩

private theorem backwards {q L : ℕ} (hq : 0<q) (hL : 0<L)
    (pos : Fin (q+1) → Fin (q*L)) (full : fullCoset q L pos) : covered q L pos := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  obtain ⟨r,_,hit⟩ := full
  intro u cop o b
  have cq : u.Coprime q := cop.of_dvd_right (dvd_mul_right _ _)
  obtain ⟨v,hv⟩ := (ZMod.isUnit_iff_coprime u q).2 cq
  let A := (o+u*r)/L
  let J : ZMod q := ((b.val : ZMod q) - (A : ZMod q)) * ↑(v⁻¹)
  have eq : (A : ZMod q)+J*u=(b.val : ZMod q) := by
    rw [←hv]; simp [J,mul_assoc]
  let j : Fin q := ⟨J.val,J.val_lt⟩
  have modEq : (A+j.val*u)%q=b.val := by
    have castEq : ((A+j.val*u : ℕ) : ZMod q) = (b.val : ZMod q) := by
      simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,j] using eq
    exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp castEq).trans (Nat.mod_eq_of_lt b.isLt)
  obtain ⟨i,hi⟩ := hit j
  use i
  unfold bin
  rw [hi,show o+u*(j.val*L+r) = o+u*r+L*(j.val*u) by ring,Nat.add_mul_div_left _ _ hL]
  exact modEq

private theorem arc_iff {q L : ℕ} (hq : 0<q) (hL : 0<L)
    (pos : Fin (q+1) → Fin (q*L)) : covered q L pos ↔ hitsArcs q L pos := by
  let M := q*L
  have hm : 0<M := Nat.mul_pos hq hL
  have cancelOffset (s : ℕ) : (M-s%M+s)%M=0 := by
    have rlt := Nat.mod_lt s hm
    have dec := Nat.mod_add_div s M
    have e : M-s%M+s=M*((s/M)+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    rw [e,Nat.mul_mod_right]
  constructor
  · intro cov u cop start
    let o := M-start%M
    obtain ⟨i,hi⟩ := cov u cop o ⟨0,hq⟩
    let x := u*(pos i).val
    let d := (o+x)%M
    have db : d/L=0 := by simpa [d,M,bin,Nat.mod_mul_left_div_self,x] using hi
    have dl : d<L := (Nat.div_eq_zero_iff.mp db).resolve_left (Nat.ne_of_gt hL)
    refine ⟨i,d,dl,?_⟩
    change x%M=(start+d)%M
    have zero := cancelOffset start
    calc
      _ = ((start+o)+x)%M := by rw [Nat.add_mod (start+o) x,Nat.add_comm start o,zero]; simp
      _ = (start+d)%M := by simp [d,Nat.add_assoc,Nat.add_mod_mod]
  · intro hit u cop o b
    let y := b.val*L
    let start := M-o%M+y
    obtain ⟨i,d,dl,he⟩ := hit u cop start
    let x := u*(pos i).val
    have zero := cancelOffset o
    have bound : y+d<M := by
      have h := Nat.mul_le_mul_right L (show b.val+1≤q by omega)
      rw [Nat.add_mul,Nat.one_mul] at h
      dsimp [y,M]
      omega
    have modSame : (o+x)%M=y+d := by
      calc
        _ = (o+(start+d))%M := by
          rw [Nat.add_mod o x,Nat.add_mod o (start+d),he]
        _ = ((M-o%M+o)+(y+d))%M := by congr 1; dsimp [start]; omega
        _ = y+d := by rw [Nat.add_mod _ (y+d),zero,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt bound]
    use i
    change (o+x)/L%q=b.val
    rw [←Nat.mod_mul_left_div_self,modSame,show y+d=d+L*b.val by dsimp [y]; ring,
      Nat.add_mul_div_left _ _ hL,Nat.div_eq_of_lt dl,Nat.zero_add]

theorem complete : H1 := by
  intro p t k hp ht pos hi
  have main : covered (p^t) (p^k) pos ↔ fullCoset (p^t) (p^k) pos :=
    ⟨forward p t hp ht k pos hi,backwards (pow_pos hp.pos _) (pow_pos hp.pos _) pos⟩
  exact ⟨main,(arc_iff (pow_pos hp.pos _) (pow_pos hp.pos _) pos).symm.trans main⟩

end OneExtraCoset

theorem OMA.solution : OMA.R_ResearchErdos142OneExtraCoset_R1.H1 := OneExtraCoset.complete

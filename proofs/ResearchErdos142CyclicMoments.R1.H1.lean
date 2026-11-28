import OMAReductions.R_ResearchErdos142CyclicMoments_R1
import Mathlib

/-! Codex for dwilfand-sys. Shifting a unit direction by a multiple of p
preserves its unit residue and cycles the second site across all q bins. -/
namespace CyclicIncidence
open OMA.R_ResearchErdos142CyclicMoments_R1

private theorem translateSum {U : Type} [Fintype U] {q : ℕ} [NeZero q]
    (f v : U → ℤ) (tr : ZMod q → U ≃ U)
    (h : ∀ u, ∑ j, f (tr j u) = v u) : (q:ℤ)*(∑u, f u)=∑u,v u := by
  calc
    _ = ∑ _j : ZMod q, ∑ u,f u := by simp
    _ = ∑ j : ZMod q, ∑ u,f (tr j u) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (Equiv.sum_comp (tr j) f).symm
    _ = ∑ u, ∑ j,f (tr j u) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun u _ => h u)

private theorem bins {q L : ℕ} [NeZero q] [NeZero L] [NeZero (q*L)]
    (z : ZMod (q*L)) : (∑j : ZMod q,hit (z+(j.val : ZMod (q*L))*(L:ZMod (q*L))))=1 := by
  classical
  let B : ZMod q := (z.val/L : ℕ)
  let weight (k : ZMod q) : ℤ := if k=0 then 1 else 0
  have hL : 0<L := Nat.pos_of_ne_zero (NeZero.ne L)
  have term (j : ZMod q) : hit (z+(j.val : ZMod (q*L))*(L:ZMod (q*L)))=weight (B+j) := by
    have rep : z+(j.val : ZMod (q*L))*(L:ZMod (q*L))=((z.val+L*j.val : ℕ):ZMod (q*L)) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    have hd : (z+(j.val : ZMod (q*L))*(L:ZMod (q*L))).val/L = (z.val/L+j.val)%q := by
      rw [rep,ZMod.val_natCast,Nat.mod_mul_left_div_self,Nat.add_mul_div_left _ _ hL]
    have modtest (k : ℕ) : ((k : ZMod q)=0) ↔ k%q=0 := by
      have eq : ((k : ZMod q)=((0:ℕ):ZMod q)) ↔ k%q=0%q :=
        ZMod.natCast_eq_natCast_iff' _ _ _
      simpa using eq
    have htest : B+j=0 ↔ (z.val/L+j.val)%q=0 := by
      simpa only [Nat.cast_add,ZMod.natCast_zmod_val,B] using modtest (z.val/L+j.val)
    have iffHit : (z+(j.val : ZMod (q*L))*(L:ZMod (q*L))).val<L ↔ B+j=0 := by
      rw [htest,←hd]
      exact ⟨Nat.div_eq_of_lt,fun h => (Nat.div_eq_zero_iff.mp h).resolve_left (Nat.ne_of_gt hL)⟩
    simp only [hit,weight,iffHit]
  calc
    _ = ∑ j : ZMod q, weight ((Equiv.addLeft B) j) :=
      Finset.sum_congr rfl (fun j _ => term j)
    _ = ∑ j : ZMod q, weight j := Equiv.sum_comp (Equiv.addLeft B) weight
    _ = 1 := by simp [weight]

private theorem regular {N p s : ℕ} [NeZero N] (hp : p.Prime) (hs : 0<s)
    (hN : N=p^s) (u x : ZMod N) : unitWeight (u+(p:ZMod N)*x)=unitWeight u := by
  classical
  subst N
  have div : p∣p^s := dvd_pow_self _ (Nat.ne_of_gt hs)
  let red := ZMod.castHom div (ZMod p)
  have criterion (v : ZMod (p^s)) : IsUnit v ↔ red v ≠ 0 := by
    rw [←ZMod.natCast_zmod_val v,map_natCast,ZMod.isUnit_natCast_iff_not_dvd_pow hp hs]
    have ex (k : ℕ) : ((k:ZMod p)=0) ↔ p∣k := by
      have eq : ((k:ZMod p)=((0:ℕ):ZMod p)) ↔ k%p=0%p := ZMod.natCast_eq_natCast_iff' _ _ _
      simpa [Nat.dvd_iff_mod_eq_zero] using eq
    exact not_congr (ex _).symm
  have redEq : red (u+(p:ZMod (p^s))*x)=red u := by
    rw [map_add,map_mul,map_natCast,ZMod.natCast_self,zero_mul,add_zero]
  simp only [unitWeight,criterion,redEq]

theorem complete : Factored := by
  classical
  intro p s q L g K _ _ _ hp hs hN hL b d hd
  let c : ZMod (q*L) := (p:ZMod (q*L))*K*↑(b⁻¹)
  have hc : c*d=(L:ZMod (q*L)) := by
    have len := congrArg (fun n : ℕ => (n : ZMod (q*L))) hL
    push_cast at len
    calc
      _ = ((p:ZMod (q*L))*K*g)*(↑(b⁻¹)*(b : ZMod (q*L))) := by rw [hd]; dsimp [c]; ring
      _ = _ := by rw [b.inv_mul,mul_one]; exact len.symm
  have one (a : ZMod (q*L)) :
      (q:ℤ)*(∑u : ZMod (q*L), unitWeight u*hit (a+u*d))=∑u : ZMod (q*L),unitWeight u := by
    apply translateSum _ _ (fun j : ZMod q => Equiv.addRight ((j.val:ZMod (q*L))*c))
    intro u
    have term (j : ZMod q) :
        unitWeight (u+(j.val:ZMod (q*L))*c)*hit (a+(u+(j.val:ZMod (q*L))*c)*d) =
        unitWeight u*hit ((a+u*d)+(j.val:ZMod (q*L))*(L:ZMod (q*L))) := by
      have sh : (j.val:ZMod (q*L))*c= (p:ZMod (q*L))*((j.val:ZMod (q*L))*(K:ZMod (q*L))*↑(b⁻¹)) := by dsimp [c]; ring
      have stable : unitWeight (u+(j.val:ZMod (q*L))*c)=unitWeight u := by
        rw [sh,regular hp hs hN]
      rw [stable,add_mul,mul_assoc,hc,add_assoc]
    calc
      _ = ∑j : ZMod q, unitWeight u*hit ((a+u*d)+(j.val:ZMod (q*L))*(L:ZMod (q*L))) :=
        Finset.sum_congr rfl (fun j _ => term j)
      _ = _ := by rw [←Finset.mul_sum,bins,mul_one]
  have area : (q:ℤ)*(∑a : ZMod (q*L),hit a)=((q*L:ℕ):ℤ) := by
    have ar := translateSum (fun a : ZMod (q*L) => hit a) (fun _ => 1)
      (fun j : ZMod q => Equiv.addRight ((j.val:ZMod (q*L))*(L:ZMod (q*L)))) (fun a => bins a)
    simpa using ar
  refine ⟨one,?_⟩
  let U := ∑u : ZMod (q*L), unitWeight u
  calc
    _ = (q:ℤ) * (∑ a : ZMod (q*L), hit a * ((q:ℤ) *
        (∑ u : ZMod (q*L), unitWeight u*hit (a+u*d)))) := by
      simp only [sq,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = (q:ℤ) * (∑ a : ZMod (q*L), hit a*U) := by simp_rw [one]; rfl
    _ = _ := by rw [←Finset.sum_mul,←mul_assoc,area]

/-- A difference outside a prime-power grid has a unit factor and leaves
one spare factor of p in the window length. -/
private theorem split (p : ℕ) (l n : ℕ) (avoid : ¬ p^l ∣ n) :
    ∃ g K b : ℕ, p^l=p*K*g ∧ n=g*b ∧ ¬p∣b := by
  induction l generalizing n with
  | zero => simp at avoid
  | succ l ih =>
    by_cases div : p∣n
    · obtain ⟨v,rfl⟩ := div
      have rest : ¬p^l∣v := by
        intro h
        apply avoid
        rw [pow_succ']
        exact Nat.mul_dvd_mul_left p h
      obtain ⟨g,K,b,hg,hv,hb⟩ := ih v rest
      exact ⟨p*g,K,b,by rw [pow_succ',hg]; ring,by rw [hv]; ring,hb⟩
    · exact ⟨1,p^l,n,by rw [pow_succ']; ring,by simp,div⟩

/-- For every off-grid difference the conditional probability is 1/q and
the two-site joint probability for a uniform translate and unit is 1/q². -/
theorem offGrid (p t l : ℕ) [NeZero p] (hp : p.Prime) (d : ZMod (p^t*p^l))
    (avoid : ¬p^l∣d.val) :
    (∀ a : ZMod (p^t*p^l),
      ((p^t:ℕ):ℤ) * (∑u : ZMod (p^t*p^l), unitWeight u * hit (a+u*d)) =
        ∑u : ZMod (p^t*p^l), unitWeight u) ∧
    ((p^t:ℕ):ℤ)^2 * (∑a : ZMod (p^t*p^l), ∑u : ZMod (p^t*p^l),
      unitWeight u * hit a * hit (a+u*d)) =
        ((p^t*p^l:ℕ):ℤ) * (∑u : ZMod (p^t*p^l), unitWeight u) := by
  have pos : 0<t+l := by
    by_contra h
    have hl : l=0 := by omega
    simp [hl] at avoid
  letI : NeZero (p^t) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p^l) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p^t*p^l) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨g,K,b,hg,hd,hb⟩ := split p l d.val avoid
  have total : p^t*p^l=p^(t+l) := (pow_add ..).symm
  have regularUnit (N : ℕ) (hN : N=p^(t+l)) : IsUnit (b:ZMod N) := by
    subst N
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp pos).2 hb
  obtain ⟨B,hB⟩ := regularUnit _ total
  apply complete p (t+l) (p^t) (p^l) g K hp pos total hg B d
  rw [hB]
  have eq := congrArg (fun n : ℕ => (n : ZMod (p^t*p^l))) hd
  simpa only [ZMod.natCast_zmod_val,Nat.cast_mul] using eq

/-- Different sites in the same grid coset can never share a window. -/
theorem onGrid {q L : ℕ} [NeZero q] [NeZero L] [NeZero (q*L)]
    (u : (ZMod (q*L))ˣ) (d a : ZMod (q*L)) (nonzero : d≠0) (on : L∣d.val) :
    hit a * hit (a+(u:ZMod (q*L))*d)=0 := by
  classical
  let y := a+(u:ZMod (q*L))*d
  by_cases ha : a.val<L
  · by_cases hy : y.val<L
    · exfalso
      apply nonzero
      let red := ZMod.castHom (show L∣q*L from dvd_mul_left L q) (ZMod L)
      have rep (v : ZMod (q*L)) : red v=(v.val:ZMod L) := by
        calc
          _ = red (v.val : ZMod (q*L)) := by rw [ZMod.natCast_zmod_val]
          _ = _ := map_natCast red _
      have rd : red d=0 := (rep d).trans ((ZMod.natCast_eq_zero_iff _ _).2 on)
      have ry : red y=red a := by simp only [y,map_add,map_mul,rd,mul_zero,add_zero]
      have same : y.val=a.val := by
        rw [rep y,rep a] at ry
        have he := (ZMod.natCast_eq_natCast_iff' _ _ _).mp ry
        simpa only [Nat.mod_eq_of_lt hy,Nat.mod_eq_of_lt ha] using he
      have equal : y=a := by
        calc
          y=(y.val:ZMod (q*L)) := (ZMod.natCast_zmod_val _).symm
          _=(a.val:ZMod (q*L)) := congrArg _ same
          _=a := ZMod.natCast_zmod_val _
      have z : (u:ZMod (q*L))*d=0 := by
        apply add_left_cancel (a:=a)
        simpa [y] using equal
      calc
        d=↑(u⁻¹)*((u:ZMod (q*L))*d) := by simp [←mul_assoc]
        _=0 := by rw [z,mul_zero]
    · change hit a * hit y=0
      simp [hit,hy]
  · simp [hit,ha]

/-- The two-site incidence kernel of the actual cyclic windows, for all differences. -/
theorem pairIncidence (p t l : ℕ) [NeZero p] (hp : p.Prime)
    (d : ZMod (p^t*p^l)) :
    ((p^t:ℕ):ℤ)^2 * (∑a : ZMod (p^t*p^l), ∑u : ZMod (p^t*p^l),
      unitWeight u * hit a * hit (a+u*d)) =
      ((p^t*p^l:ℕ):ℤ) * (∑u : ZMod (p^t*p^l), unitWeight u) *
        (if d=0 then ((p^t:ℕ):ℤ) else if p^l∣d.val then 0 else 1) := by
  classical
  by_cases diagonal : d=0
  · subst d
    simp only [mul_zero,add_zero,if_pos rfl]
    have idem (a u : ZMod (p^t*p^l)) :
        unitWeight u * hit a * hit a=unitWeight u * hit a := by
      unfold hit
      split <;> simp
    simp_rw [idem,←Finset.sum_mul]
    rw [←Finset.mul_sum]
    have area := translateSum (fun a : ZMod (p^t*p^l) => hit a) (fun _ => 1)
      (fun j : ZMod (p^t) => Equiv.addRight ((j.val:ZMod (p^t*p^l))*((p^l:ℕ):ZMod (p^t*p^l))))
      (fun a => bins a)
    have area' : ((p^t:ℕ):ℤ)*(∑a : ZMod (p^t*p^l),hit a)=((p^t*p^l:ℕ):ℤ) := by
      simpa using area
    rw [←area']
    simp <;> ring
  · by_cases grid : p^l∣d.val
    · have vanish (a u : ZMod (p^t*p^l)) : unitWeight u*hit a*hit (a+u*d)=0 := by
        by_cases unit : IsUnit u
        · obtain ⟨v,rfl⟩ := unit
          rw [mul_assoc,onGrid v d a diagonal grid,mul_zero]
        · simp [unitWeight,unit]
      simp [diagonal,grid,vanish]
    · simpa [diagonal,grid] using (offGrid p t l hp d grid).2

/-- Joint incidence for arbitrary affine images of two sites, translated
by the same origin and multiplied by the same unit. -/
theorem affinePair (p t l : ℕ) [NeZero p] (hp : p.Prime)
    (x y : ZMod (p^t*p^l)) :
    ((p^t:ℕ):ℤ)^2 * (∑a : ZMod (p^t*p^l), ∑u : ZMod (p^t*p^l),
      unitWeight u * hit (a+u*x) * hit (a+u*y)) =
      ((p^t*p^l:ℕ):ℤ) * (∑u : ZMod (p^t*p^l), unitWeight u) *
        (if y-x=0 then ((p^t:ℕ):ℤ) else if p^l∣(y-x).val then 0 else 1) := by
  classical
  let f (u a : ZMod (p^t*p^l)) := unitWeight u*hit a*hit (a+u*(y-x))
  have shift (u : ZMod (p^t*p^l)) :
      (∑a : ZMod (p^t*p^l), unitWeight u*hit (a+u*x)*hit (a+u*y))=∑a,f u a := by
    calc
      _ = ∑a,f u ((Equiv.addRight (u*x)) a) := by
        apply Finset.sum_congr rfl
        intro a _
        have h : a+u*y=(a+u*x)+u*(y-x) := by ring
        change unitWeight u*hit (a+u*x)*hit (a+u*y)=
          unitWeight u*hit (a+u*x)*hit ((a+u*x)+u*(y-x))
        rw [h]
      _ = _ := Equiv.sum_comp _ _
  calc
    _ = ((p^t:ℕ):ℤ)^2 * (∑ u,∑ a,f u a) := by rw [Finset.sum_comm]; simp_rw [shift]
    _ = _ := by rw [Finset.sum_comm]; exact pairIncidence p t l hp (y-x)

/-- The unnormalized weighted second moment, on the actual prime-power circle. -/
theorem weighted (p t l : ℕ) [NeZero p] (hp : p.Prime)
    (w : ZMod (p^t*p^l) → ℤ) :
    ((p^t:ℕ):ℤ)^2 * (∑a : ZMod (p^t*p^l), ∑u : ZMod (p^t*p^l),
      unitWeight u * (∑x,hit (a+u*x)*w x)^2) =
      ((p^t*p^l:ℕ):ℤ) * (∑u : ZMod (p^t*p^l), unitWeight u) *
        ((∑x,w x)^2 + ((p^t:ℕ):ℤ)*(∑x,w x^2) -
          ∑x,∑y,if p^l∣(y-x).val then w x*w y else 0) := by
  classical
  let Z := ZMod (p^t*p^l)
  let Q : ℤ := (p^t:ℕ)
  let A := ((p^t*p^l:ℕ):ℤ)*(∑u : Z,unitWeight u)
  let K (x y : Z) : ℤ := if y-x=0 then Q else if p^l∣(y-x).val then 0 else 1
  let f (a u x y : Z) : ℤ :=
    Q^2*(unitWeight u*hit (a+u*x)*hit (a+u*y))*w x*w y
  have entry (x y : Z) :
      K x y*w x*w y=(w x*w y-(if p^l∣(y-x).val then w x*w y else 0))+
        (if y=x then Q*w x^2 else 0) := by
    by_cases eq : y=x
    · subst y; simp [K]; ring
    · have neq : y-x≠0 := sub_ne_zero.mpr eq
      by_cases grid : p^l∣(y-x).val <;> simp [K,neq,eq,grid]
  have evaluate (x y : Z) : (∑a,∑u,f a u x y)=A*(K x y*w x*w y) := by
    calc
      _ = (Q^2*(∑a : Z,∑u : Z,unitWeight u*hit (a+u*x)*hit (a+u*y)))*w x*w y := by
        simp only [Finset.sum_mul,Finset.mul_sum,f]
      _ = _ := by rw [show Q^2*(∑a : Z,∑u : Z,unitWeight u*hit (a+u*x)*hit (a+u*y))=A*K x y from affinePair p t l hp x y]; ring
  have shuffle : (∑a,∑u,∑x,∑y,f a u x y) = ∑x,∑y,∑a,∑u,f a u x y := by
    calc
      _ = ∑a,∑x,∑u,∑y,f a u x y := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑x,∑a,∑u,∑y,f a u x y := Finset.sum_comm
      _ = ∑x,∑a,∑y,∑u,f a u x y := Finset.sum_congr rfl
        (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
      _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have all : (∑x,∑y,w x*w y)=(∑x,w x)^2 := by
    simp only [sq,Finset.sum_mul,Finset.mul_sum]
  have diag : (∑ x,∑y,if y=x then Q*w x^2 else 0)=Q*(∑x,w x^2) := by
    simp [Finset.mul_sum]
  have total : (∑x,∑y,K x y*w x*w y)=(∑x,w x)^2+Q*(∑x,w x^2)-
      ∑x,∑y,if p^l∣(y-x).val then w x*w y else 0 := by
    simp_rw [entry]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [all,diag]
    ring
  calc
    _ = ∑a,∑u,∑x,∑y,f a u x y := by
      simp only [sq,Finset.sum_mul,Finset.mul_sum,f]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u _ =>
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      dsimp [Q]
      ring
    _ = ∑x,∑y,A*(K x y*w x*w y) := by rw [shuffle]; simp_rw [evaluate]
    _ = _ := by rw [←Finset.mul_sum]; simp_rw [←Finset.mul_sum]; rw [total]

end CyclicIncidence

theorem OMA.solution : OMA.R_ResearchErdos142CyclicMoments_R1.H1 := by
  intro p t l _ hp
  exact ⟨fun d hd => (CyclicIncidence.offGrid p t l hp d hd).1,
    CyclicIncidence.affinePair p t l hp,CyclicIncidence.weighted p t l hp⟩

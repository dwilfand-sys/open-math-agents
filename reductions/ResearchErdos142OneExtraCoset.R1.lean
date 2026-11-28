import OMAReductions.R_ResearchErdos142ShearKernel_R1
import Mathlib

/-! A (q+1)-element mask on the discrete circle of order q*L blocks all
unit-step progressions of length L exactly when it contains a q-coset. -/
namespace OMA.R_ResearchErdos142OneExtraCoset_R1
open OMA.R_ResearchErdos142ShearMajority_R1

def covered (q L : ℕ) (pos : Fin (q+1) → Fin (q*L)) : Prop :=
  ∀ u : ℕ, Nat.Coprime u (q*L) → ∀ (o : ℕ) (b : Fin q),
    ∃ i, bin q L o u (pos i).val = b.val

def fullCoset (q L : ℕ) (pos : Fin (q+1) → Fin (q*L)) : Prop :=
  ∃ r : ℕ, r<L ∧ ∀ b : Fin q, ∃ i, (pos i).val=b.val*L+r

/-- Literal containment of a cyclic interval of unit order is equivalent to
bin occupancy at all origins. The offset d is the positive length-L arc
coordinate in the unit image; endpoint residues are modulo the true period. -/
def hitsArcs (q L : ℕ) (pos : Fin (q+1) → Fin (q*L)) : Prop :=
  ∀ u : ℕ, u.Coprime (q*L) → ∀ start : ℕ, ∃ i, ∃ d < L,
    (u*(pos i).val)%(q*L)=(start+d)%(q*L)

def H1 : Prop := ∀ (p t k : ℕ), p.Prime → 0<t →
  ∀ pos : Fin (p^t+1) → Fin (p^t*p^k), Function.Injective pos →
    (covered (p^t) (p^k) pos ↔ fullCoset (p^t) (p^k) pos) ∧
    (hitsArcs (p^t) (p^k) pos ↔ fullCoset (p^t) (p^k) pos)

end OMA.R_ResearchErdos142OneExtraCoset_R1

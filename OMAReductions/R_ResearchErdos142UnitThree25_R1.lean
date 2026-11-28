import Mathlib

/-! A subset of the cyclic group of order 25 is its 25-bit membership mask.
The number of set bits is at most 25, so population addition cannot overflow.
The masks for the five single residue classes mod 5 are multiples of 1082401
by successive powers of two. Every possible unit step is listed explicitly. -/
namespace OMA.R_ResearchErdos142UnitThree25_R1

def threeFree (m : BitVec 25) : Prop :=
    (m &&& m.rotateRight 1 &&& m.rotateRight 2) = 0 ∧
    (m &&& m.rotateRight 2 &&& m.rotateRight 4) = 0 ∧
    (m &&& m.rotateRight 3 &&& m.rotateRight 6) = 0 ∧
    (m &&& m.rotateRight 4 &&& m.rotateRight 8) = 0 ∧
    (m &&& m.rotateRight 6 &&& m.rotateRight 12) = 0 ∧
    (m &&& m.rotateRight 7 &&& m.rotateRight 14) = 0 ∧
    (m &&& m.rotateRight 8 &&& m.rotateRight 16) = 0 ∧
    (m &&& m.rotateRight 9 &&& m.rotateRight 18) = 0 ∧
    (m &&& m.rotateRight 11 &&& m.rotateRight 22) = 0 ∧
    (m &&& m.rotateRight 12 &&& m.rotateRight 24) = 0 ∧
    (m &&& m.rotateRight 13 &&& m.rotateRight 1) = 0 ∧
    (m &&& m.rotateRight 14 &&& m.rotateRight 3) = 0 ∧
    (m &&& m.rotateRight 16 &&& m.rotateRight 7) = 0 ∧
    (m &&& m.rotateRight 17 &&& m.rotateRight 9) = 0 ∧
    (m &&& m.rotateRight 18 &&& m.rotateRight 11) = 0 ∧
    (m &&& m.rotateRight 19 &&& m.rotateRight 13) = 0 ∧
    (m &&& m.rotateRight 21 &&& m.rotateRight 17) = 0 ∧
    (m &&& m.rotateRight 22 &&& m.rotateRight 19) = 0 ∧
    (m &&& m.rotateRight 23 &&& m.rotateRight 21) = 0 ∧
    (m &&& m.rotateRight 24 &&& m.rotateRight 23) = 0

def population (m : BitVec 25) : BitVec 25 :=
    ((m >>> (0 : Nat)) &&& 1) +
    ((m >>> (1 : Nat)) &&& 1) +
    ((m >>> (2 : Nat)) &&& 1) +
    ((m >>> (3 : Nat)) &&& 1) +
    ((m >>> (4 : Nat)) &&& 1) +
    ((m >>> (5 : Nat)) &&& 1) +
    ((m >>> (6 : Nat)) &&& 1) +
    ((m >>> (7 : Nat)) &&& 1) +
    ((m >>> (8 : Nat)) &&& 1) +
    ((m >>> (9 : Nat)) &&& 1) +
    ((m >>> (10 : Nat)) &&& 1) +
    ((m >>> (11 : Nat)) &&& 1) +
    ((m >>> (12 : Nat)) &&& 1) +
    ((m >>> (13 : Nat)) &&& 1) +
    ((m >>> (14 : Nat)) &&& 1) +
    ((m >>> (15 : Nat)) &&& 1) +
    ((m >>> (16 : Nat)) &&& 1) +
    ((m >>> (17 : Nat)) &&& 1) +
    ((m >>> (18 : Nat)) &&& 1) +
    ((m >>> (19 : Nat)) &&& 1) +
    ((m >>> (20 : Nat)) &&& 1) +
    ((m >>> (21 : Nat)) &&& 1) +
    ((m >>> (22 : Nat)) &&& 1) +
    ((m >>> (23 : Nat)) &&& 1) +
    ((m >>> (24 : Nat)) &&& 1)

def twoResidues (m : BitVec 25) : Prop :=
    m = (1082401 ||| 2164802) ∨
    m = (1082401 ||| 4329604) ∨
    m = (1082401 ||| 8659208) ∨
    m = (1082401 ||| 17318416) ∨
    m = (2164802 ||| 4329604) ∨
    m = (2164802 ||| 8659208) ∨
    m = (2164802 ||| 17318416) ∨
    m = (4329604 ||| 8659208) ∨
    m = (4329604 ||| 17318416) ∨
    m = (8659208 ||| 17318416)

def H1 : Prop :=
  ∀ m : BitVec 25, (threeFree m ∧ (10 : BitVec 25) ≤ population m) ↔ twoResidues m

end OMA.R_ResearchErdos142UnitThree25_R1

import OMAReductions.R_ResearchErdos142UnitThree25_R1
import Mathlib

/- Codex for @dwilfand-sys. Exhaust the five base-32 digits of the membership
mask. A lowMask containing a progression rules out all of its extensions.
Every finite computation below is reduced by the Lean kernel. -/
namespace UnitThree25
open OMA.R_ResearchErdos142UnitThree25_R1

private instance (m : BitVec 25) : Decidable (threeFree m) := by
  unfold threeFree
  infer_instance
private instance (m : BitVec 25) : Decidable (twoResidues m) := by
  unfold twoResidues
  infer_instance

private theorem rotateAnd (m z : BitVec 25) (d : ℕ) :
    (m &&& z).rotateRight d = m.rotateRight d &&& z.rotateRight d := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight]
  split <;> rfl

private theorem trim (m z : BitVec 25) (a b : ℕ)
    (h : m &&& m.rotateRight a &&& m.rotateRight b = 0) :
    (m &&& z) &&& (m &&& z).rotateRight a &&& (m &&& z).rotateRight b = 0 := by
  rw [rotateAnd, rotateAnd]
  calc
    _ = (m &&& m.rotateRight a &&& m.rotateRight b) &&&
        (z &&& z.rotateRight a &&& z.rotateRight b) := by ac_rfl
    _ = 0 := by rw [h]; simp

private theorem lowMask (m : BitVec 25) (hm : threeFree m) (i : ℕ) (hi : 2^i ≤ 2^25) :
    threeFree (BitVec.ofNat 25 (m.toNat % 2^i)) := by
  let z := BitVec.ofNat 25 (2^i-1)
  have eq : BitVec.ofNat 25 (m.toNat % 2^i) = m &&& z := by
    apply BitVec.eq_of_toNat_eq
    have hp : 0 < (2:ℕ)^i := by positivity
    have hmask : 2^i-1 < 2^25 := by omega
    have hmod : m.toNat%2^i < 2^25 := lt_of_lt_of_le (Nat.mod_lt _ hp) hi
    simp only [z, BitVec.toNat_ofNat, BitVec.toNat_and, Nat.mod_eq_of_lt hmask,
      Nat.mod_eq_of_lt hmod, Nat.and_two_pow_sub_one_eq_mod]
  rw [eq]
  rcases hm with ⟨h1, h2, h3, h4, h6, h7, h8, h9, h11, h12, h13, h14, h16, h17, h18, h19, h21, h22, h23, h24⟩
  exact ⟨trim m z 1 2 h1,
    trim m z 2 4 h2,
    trim m z 3 6 h3,
    trim m z 4 8 h4,
    trim m z 6 12 h6,
    trim m z 7 14 h7,
    trim m z 8 16 h8,
    trim m z 9 18 h9,
    trim m z 11 22 h11,
    trim m z 12 24 h12,
    trim m z 13 1 h13,
    trim m z 14 3 h14,
    trim m z 16 7 h16,
    trim m z 17 9 h17,
    trim m z 18 11 h18,
    trim m z 19 13 h19,
    trim m z 21 17 h21,
    trim m z 22 19 h22,
    trim m z 23 21 h23,
    trim m z 24 23 h24⟩

private def scan : ℕ → ℕ → ℕ → Bool
  | 0, _, v =>
    let m := BitVec.ofNat 25 v
    if threeFree m then decide ((10 : BitVec 25) ≤ population m → twoResidues m) else true
  | n+1, p, v =>
    if threeFree (BitVec.ofNat 25 v) then
      (List.range 32).all fun b => scan n (p*32) (v+p*b)
    else true

private theorem advance {n p v b : ℕ} (hf : threeFree (BitVec.ofNat 25 v))
    (hs : scan (n+1) p v = true) (hb : b<32) : scan n (p*32) (v+p*b) = true := by
  rw [scan, if_pos hf, List.all_eq_true] at hs
  exact hs b (List.mem_range.mpr hb)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem checked : scan 5 1 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem main : OMA.R_ResearchErdos142UnitThree25_R1.H1 := by
  intro m
  constructor
  · rintro ⟨hm, hc⟩
    have s0 : scan 5 1 (m.toNat % 1) = true := by simpa using checked
    have s1a := advance (n := 4) (p := 1) (v := m.toNat % 1)
      (b := m.toNat / 1 % 32) (lowMask m hm 0 (by decide)) s0
      (Nat.mod_lt _ (by decide))
    have d1 : m.toNat % 1 + 1 * (m.toNat / 1 % 32) = m.toNat % 32 := by omega
    rw [d1] at s1a
    have s1 : scan 4 32 (m.toNat % 32) = true := s1a
    have s2a := advance (n := 3) (p := 32) (v := m.toNat % 32)
      (b := m.toNat / 32 % 32) (lowMask m hm 5 (by decide)) s1
      (Nat.mod_lt _ (by decide))
    have d2 : m.toNat % 32 + 32 * (m.toNat / 32 % 32) = m.toNat % 1024 := by omega
    rw [d2] at s2a
    have s2 : scan 3 1024 (m.toNat % 1024) = true := s2a
    have s3a := advance (n := 2) (p := 1024) (v := m.toNat % 1024)
      (b := m.toNat / 1024 % 32) (lowMask m hm 10 (by decide)) s2
      (Nat.mod_lt _ (by decide))
    have d3 : m.toNat % 1024 + 1024 * (m.toNat / 1024 % 32) = m.toNat % 32768 := by omega
    rw [d3] at s3a
    have s3 : scan 2 32768 (m.toNat % 32768) = true := s3a
    have s4a := advance (n := 1) (p := 32768) (v := m.toNat % 32768)
      (b := m.toNat / 32768 % 32) (lowMask m hm 15 (by decide)) s3
      (Nat.mod_lt _ (by decide))
    have d4 : m.toNat % 32768 + 32768 * (m.toNat / 32768 % 32) = m.toNat % 1048576 := by omega
    rw [d4] at s4a
    have s4 : scan 1 1048576 (m.toNat % 1048576) = true := s4a
    have s5a := advance (n := 0) (p := 1048576) (v := m.toNat % 1048576)
      (b := m.toNat / 1048576 % 32) (lowMask m hm 20 (by decide)) s4
      (Nat.mod_lt _ (by decide))
    have d5 : m.toNat % 1048576 + 1048576 * (m.toNat / 1048576 % 32) = m.toNat % 33554432 := by omega
    rw [d5] at s5a
    have s5 : scan 0 33554432 (m.toNat % 33554432) = true := s5a
    have hlt : m.toNat < 33554432 := m.isLt
    rw [Nat.mod_eq_of_lt hlt] at s5
    have finish : (10 : BitVec 25) ≤ population m → twoResidues m := by
      simpa only [scan, BitVec.ofNat_toNat, if_pos hm, decide_eq_true_eq] using s5
    exact finish hc
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> subst m <;> decide +kernel
end UnitThree25

theorem OMA.solution : OMA.R_ResearchErdos142UnitThree25_R1.H1 := UnitThree25.main

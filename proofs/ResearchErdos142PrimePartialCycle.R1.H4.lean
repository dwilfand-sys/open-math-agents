import OMAReductions.R_ResearchErdos142PrimePartialCycle_R1

/-! A prime modulus has the complete-residue property used by the partial-cycle construction. -/

namespace Erdos142PrimePartialCyclePrime

open OMA.R_ResearchErdos142PrimePartialCycle_R1

theorem prime_completeResidues {p : ℕ} (hp : p.Prime) : completeResidues p := by
  intro a d hnonzero
  have hnotdvd : ¬p ∣ d := by
    intro hpd
    exact hnonzero (Nat.dvd_iff_mod_eq_zero.mp hpd)
  have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hnotdvd).symm
  obtain ⟨v, -, hv⟩ := exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  let i := ((p - a % p) * v) % p
  refine ⟨i, Nat.mod_lt _ hp.pos, ?_⟩
  have hi : i ≡ (p - a % p) * v [MOD p] := by
    simp only [i, Nat.ModEq, Nat.mod_mod]
  have hinv : v * d ≡ 1 [MOD p] := by
    simp only [Nat.ModEq]
    simpa [Nat.mul_comm] using hv
  have ha : a ≡ a % p [MOD p] := by
    simp only [Nat.ModEq, Nat.mod_mod]
  have hid : i * d ≡ (p - a % p) * 1 [MOD p] := by
    calc
      i * d ≡ ((p - a % p) * v) * d [MOD p] := hi.mul_right d
      _ = (p - a % p) * (v * d) := by ring
      _ ≡ (p - a % p) * 1 [MOD p] := hinv.mul_left (p - a % p)
  have hs := ha.add hid
  have hsum : a % p + (p - a % p) * 1 = p := by
    have hlt := Nat.mod_lt a hp.pos
    omega
  have hz : a % p + (p - a % p) * 1 ≡ 0 [MOD p] := by
    simp only [hsum, Nat.ModEq, Nat.mod_self, zero_mod]
  simpa only [Nat.ModEq, zero_mod] using hs.trans hz

end Erdos142PrimePartialCyclePrime

theorem OMA.solution : OMA.R_ResearchErdos142PrimePartialCycle_R1.H4 := by
  intro p hp
  exact Erdos142PrimePartialCyclePrime.prime_completeResidues hp

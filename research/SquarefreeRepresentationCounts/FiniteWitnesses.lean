import Mathlib

/-!
# Positive square plus squarefree representations

For each of the 101 levels printed in OEIS A085264, a positive integer at
most 10038 has exactly that many representations. The final theorem verifies
that each witness in the table is the first positive integer at its level. The nine values
listed in A085266 are exactly the single-representation integers through
1024. These are finite certificates for the two conjectures.

Source: https://oeis.org/A085264 and https://oeis.org/A085266.
Proof and computation developed by Codex for @dwilfand-sys. The six
axiom reports were checked in Mathlib with Lean 4.37.0-rc1, 27 November 2026.
-/

namespace SquarefreeCounts

def squarefreeCheck (T r : ℕ) : Bool :=
  (List.range (T+1)).all fun d => decide (d < 2 ∨ ¬ d*d ∣ r)

theorem squarefreeCheck_iff {T r : ℕ} (hr : 0 < r) (hbound : r < (T+1)^2) :
    squarefreeCheck T r = true ↔ Squarefree r := by
  rw [squarefreeCheck, List.all_eq_true, Nat.squarefree_iff_prime_squarefree]
  simp only [List.mem_range, decide_eq_true_eq]
  constructor
  · intro h p hp hd
    have hle := Nat.le_of_dvd hr hd
    have plt : p < T+1 := by nlinarith
    exact (h p plt).elim (by have := hp.two_le; omega) (fun bad => bad hd)
  · intro h d _
    by_cases small : d < 2
    · exact Or.inl small
    · right
      intro hd
      have hprime := Nat.minFac_prime (by omega : d ≠ 1)
      have hpdiv := Nat.minFac_dvd d
      exact h d.minFac hprime ((mul_dvd_mul hpdiv hpdiv).trans hd)

def checkedCount (T n : ℕ) : ℕ :=
  ((Finset.range (T+1)).filter fun k => 0 < k ∧ k^2 < n ∧ squarefreeCheck T (n-k^2) = true).card

def representations (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt+1)).filter fun k => 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)).card

theorem checkedCount_eq {T n : ℕ} (hb : n < (T+1)^2) : checkedCount T n = representations n := by
  unfold checkedCount representations
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hk, hkn, hs⟩
    exact ⟨by have := Nat.le_sqrt'.mpr hkn.le; omega, hk, hkn,
      (squarefreeCheck_iff (by omega) (by omega : n-k^2 < (T+1)^2)).mp hs⟩
  · rintro ⟨_, hk, hkn, hs⟩
    have kt : k < T+1 := by nlinarith
    exact ⟨kt, hk, hkn,
      (squarefreeCheck_iff (by omega) (by omega : n-k^2 < (T+1)^2)).mpr hs⟩

def singles : List ℕ := [2,3,4,5,8,9,25,29,61]

set_option maxHeartbeats 1200000 in
theorem prefixCert : (List.range 1025).all (fun n => decide (checkedCount 32 n = 1 ↔ n ∈ singles)) = true := by decide +kernel

theorem prefix_single {n : ℕ} (h : n < 1025) : representations n = 1 ↔ n ∈ singles := by
  have hcheck := List.all_eq_true.mp prefixCert n (List.mem_range.mpr h)
  have eqn := checkedCount_eq (T:=32) (n:=n) (by omega)
  simpa only [decide_eq_true_eq, eqn] using hcheck

#print axioms prefix_single
#print axioms checkedCount_eq

def smallPrimes : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
def primeCheck (r : ℕ) : Bool := smallPrimes.all fun p => decide (¬ p*p ∣ r)
private theorem smallPrimes_spec {p : ℕ} : p ∈ smallPrimes ↔ p.Prime ∧ p ≤ 100 := by
  constructor
  · intro hm
    unfold smallPrimes at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · rintro ⟨hp,hb⟩
    interval_cases p <;> first | decide | norm_num at hp

theorem primeCheck_iff {r : ℕ} (hr : 0 < r) (hb : r < 101^2) : primeCheck r = true ↔ Squarefree r := by
  rw [primeCheck, List.all_eq_true, Nat.squarefree_iff_prime_squarefree]
  simp only [decide_eq_true_eq]
  constructor
  · intro h p hp hd
    have le := Nat.le_of_dvd hr hd
    exact h p (smallPrimes_spec.mpr ⟨hp,by nlinarith⟩) hd
  · intro h p hm
    exact h p (smallPrimes_spec.mp hm).1

def primeCount (n : ℕ) : ℕ := ((Finset.range 101).filter fun k =>
  0 < k ∧ k^2 < n ∧ primeCheck (n-k^2) = true).card

theorem primeCount_eq {n : ℕ} (hb : n < 101^2) : primeCount n = representations n := by
  rw [← checkedCount_eq (T:=100) (n:=n) (by omega)]
  unfold primeCount checkedCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨hl,hk,hn,h⟩ <;> refine ⟨hl,hk,hn,?_⟩
  · exact (squarefreeCheck_iff (by omega) (by omega : n-k^2 < (100+1)^2)).mpr ((primeCheck_iff (by omega) (by omega)).mp h)
  · exact (primeCheck_iff (by omega) (by omega : n-k^2 < 101^2)).mpr ((squarefreeCheck_iff (by omega) (by omega)).mp h)

def witnesses : List ℕ := [1,2,6,11,23,30,38,62,71,83,110,138,155,182,203,227,263,302,327,383,435,447,503,542,602,635,707,755,798,878,915,983,1055,1118,1182,1295,1343,1403,1463,1547,1643,1722,1778,1883,1995,2063,2162,2238,2327,2442,2567,2618,2730,2855,2967,3090,3143,3302,3395,3527,3647,3962,3863,4070,4142,4290,4535,4542,4703,4847,4935,5207,5358,5423,5543,5738,5970,6047,6195,6398,6467,6690,6767,7035,7103,7262,7482,7598,7763,8027,8315,8378,8543,8690,8942,9107,9407,9687,9638,10038,10023]
def witness (j : ℕ) : ℕ := witnesses[j]?.getD 0
def witnessOK (j : ℕ) : Bool := decide (0 < witness j ∧ witness j ≤ 10038 ∧ primeCount (witness j) = j)

set_option maxHeartbeats 1200000 in
theorem level_cert : (List.range 101).all witnessOK = true := by decide +kernel

theorem realizes_levels_through_100 {j : ℕ} (hj : j ≤ 100) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 10038 ∧ representations n = j := by
  have h := List.all_eq_true.mp level_cert j (List.mem_range.mpr (by omega))
  have h' : 0 < witness j ∧ witness j ≤ 10038 ∧ primeCount (witness j) = j := of_decide_eq_true h
  exact ⟨witness j,h'.1,h'.2.1,(primeCount_eq (n:=witness j) (by omega)).symm.trans h'.2.2⟩
#print axioms primeCount_eq
theorem least_for_listed_levels {j : ℕ} (hj : j ≤ 100) :
    ∃ m : ℕ, m ≤ 10038 ∧ IsLeast {n : ℕ | 0 < n ∧ representations n = j} m := by
  obtain ⟨n,hn,hb,hj'⟩ := realizes_levels_through_100 hj
  have existsLevel : ∃ x : ℕ, 0 < x ∧ representations x = j := ⟨n,hn,hj'⟩
  exact ⟨Nat.find existsLevel,(Nat.find_min' existsLevel ⟨hn,hj'⟩).trans hb,
    Nat.find_spec existsLevel,fun _ hx => Nat.find_min' existsLevel hx⟩
#print axioms realizes_levels_through_100
#print axioms least_for_listed_levels


/-- Bit r records whether r is squarefree. The kernel checks every positive entry against the prime sieve. -/
def squarefreeBits : ℕ := 0x66e8eceeee6eaece66e6eaa4eeee4aaeceeae6eae4eeee68aecee8e6eae8eeee6e2eceee26eaecceee6eaeceeee6eaeccaee6cacceeae6eaec6e6e6e268eece6caeceaee6eaec6eee4eaecaeec6eacceeee2ea6cee6e2eaececec6aaec6eee66aecee2c6eaeceeee6eaeceee66e2ecaeee6e8ecaeee6eaece6ec6eaaceeee4eaeceeec6eaa4e6e42aaeceece2eaeceeee6e2cceeea6eaccceee6eaeceeee66aeceaee6eac8eeee6eaecee4a6eae8eeee6ca6ceeee66aec6eee6eaeceee86eaeceeee6e868eeee2eaece4ee6a8eceeec66aecee8e6eaaceeee66aecece66eaecaeee6e8ecaeee6eae4e6ee6eaaceeae4eaec6eee6cae4eeee6aaeceece6eaeceee26e2eceeea62a6cccee6eaecceee6e8eceaee6eacceeee6ea6cee2e6eae8eaee6caeceeee4eaec6eee6eaeceeec6eaecee6e6ca6ceeee2aaececee2eaaceeee66aeceeae2eaeceeee2e2ecece66eaecaeee6e8eceeec6eaece6e66eaaceeee4eaece6ee6eae4eeee2aae4eece6eaccaeee6e2eceeea6eaecceae66aeceeee6eaa8eaee6e8cceece6caccec6e6e2e8ceee6caec6eee6eaec6eea6eaeceee46e8eceeee6ea6ceee626aece4ee6eaece6ee66aaceeae6eaececee6eaeceee66eaecaeee6e8a4ceee6eaece6ae6aaaceeee4caeceeee6eae4eeee4aacceec66eaeceeee6e26ceeea6e8ecceee6eaeceeee6caeceaee6ea4ceeee6eaecea6e6eae8eeee4cae4eeee6e2ec6eee6eaecee6c66aeceeee6aa6caeee2aaececee6eaecee6e66aeceeae6e2eceaee6eaecaec66aaeca6ec6e8eceeee6e2ece6ee6eaace6ee4ea6ceeee2eae4eeee6aaccecce6eaeceeae6e2eceeea662ecceee6e2e8eeee6eaeceace6eacceeee6eaecae6a6eaa824ee6caeceeea6eaec6eec6e8eceeec6e8ecceee6ea6ceeee2eaececee6e8aceeee66aececae6eaece6ee6eacceee66eae4aeee6e8eceeae2eaece6ee6caaceeee4eaeceeee4eac4eee66aaeceece2eaeceaee6e2ecceea6ea6cceee6eaeceeee6ea6ceaee66acceaec6eaecee6e4eae8eeee6cae8e6ee6eaec6e6e6eaaceeec6aaeceece6ea64eeee2eaececee6eaecee6e662eceeae6eaecaeee6eaeceee46eacc2eee6e8c8eee62eaece6ee6eaaceeea0eae8eeee6eac4eeee68aeceece6e8eceeee462eceeea6eae8ceee6eaeceece6eaaceaee6eacceeee6eaec6e6e6eae8eeea6caec6eee6e8e42eee6eaaceeec6eaeceeee6ea6ceeee2eaacecee6eaececee66aeceeae6eaeceeee6eae0e6e46eaecaeae6e8ececee6cae4e6ee6eaaceaee4eaeceee66eae4eeae6a8eceece6eaecceee6e2eceeea6ca6c46ee6ea6ceeee6eaeceaee6eacceeee4eaecee6e2eae8eeee6caecee666eaec6eee6aaeceeec6eaccecee6ea6caeee2eaececee6e2eceeee66aec8eae6eaec6eec6eaeceee66eaecaeee6e8ace6ee6eaece6ee26a8ceeee4ea4cceee6eae4eeee6aaecaece66aeceaae0e2e8eeea6eaeccece6eaece6ee4eaeceaee6eacc6eee6eaecee6a6eae8ceee6c8eceeee6eaec6cee6eaecee6c6eaeceeee6ea2ceeee2eaececee6aaeceee666aeceeae6eae4eeee6eaece6a66eaacaeee6c8ecaeee6eaece6ee4eaaceee64eaeceeee6eae4e6ee6a0cccece6eaeceeee6e2eceeea6ea6c8aee6eaeceaee6eaeceaee4eacceeec6eaecea6e6eae8ee6e4caece6ee6aaec6eee6eaeceeec6eaeceeee6ea6ce4ee2e2acecee6eaecacee66aeceeac2eaeceeee6eaeceee64eaeca6ee6e8cceeee2eaece6ee6ea8ceeee4eaecee

private def checkBlocks (f : ℕ → Bool) : Bool :=
  (List.range 40).all fun block => (List.range 256).all fun col => f (256*block+col)

private theorem of_checkBlocks {f : ℕ → Bool} (h : checkBlocks f = true)
    {n : ℕ} (hn : n < 10240) : f n = true := by
  have hb := List.all_eq_true.mp h (n/256) (List.mem_range.mpr (by omega))
  have hc := List.all_eq_true.mp hb (n%256) (List.mem_range.mpr (by omega))
  simpa only [Nat.div_add_mod] using hc

private def entryOK (r : ℕ) : Bool :=
  decide (0 < r → r ≤ 10038 → squarefreeBits.testBit r = primeCheck r)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem allEntries : checkBlocks entryOK = true := by decide +kernel

private theorem bit_iff {r : ℕ} (hpos : 0 < r) (hb : r ≤ 10038) :
    squarefreeBits.testBit r = true ↔ Squarefree r := by
  have h := of_checkBlocks allEntries (n:=r) (by omega)
  have he : 0 < r → r ≤ 10038 → squarefreeBits.testBit r = primeCheck r := of_decide_eq_true h
  rw [he hpos hb, primeCheck_iff hpos (by omega)]

def maskCount (n : ℕ) : ℕ := ((Finset.range 101).filter fun k =>
  0 < k ∧ k^2 < n ∧ squarefreeBits.testBit (n-k^2) = true).card

theorem maskCount_eq {n : ℕ} (hb : n ≤ 10038) : maskCount n = representations n := by
  rw [← primeCount_eq (n:=n) (by omega)]
  unfold maskCount primeCount
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  constructor <;> rintro ⟨hl,hk,hn,h⟩ <;> refine ⟨hl,hk,hn,?_⟩
  · exact (primeCheck_iff (by omega) (by omega : n-k^2 < 101^2)).mpr ((bit_iff (by omega) (by omega)).mp h)
  · exact (bit_iff (by omega) (by omega : n-k^2 ≤ 10038)).mpr ((primeCheck_iff (by omega) (by omega)).mp h)

private def earliestOK (n : ℕ) : Bool :=
  decide (0 < n → n ≤ 10038 → witness (maskCount n) ≤ n)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
private theorem allEarliest : checkBlocks earliestOK = true := by decide +kernel

theorem exact_first_occurrences {j : ℕ} (hj : j ≤ 100) :
    IsLeast {n : ℕ | 0 < n ∧ representations n = j} (witness j) := by
  have h := List.all_eq_true.mp level_cert j (List.mem_range.mpr (by omega))
  have hw : 0 < witness j ∧ witness j ≤ 10038 ∧ primeCount (witness j) = j := of_decide_eq_true h
  refine ⟨⟨hw.1,(primeCount_eq (n:=witness j) (by omega)).symm.trans hw.2.2⟩,?_⟩
  rintro n ⟨hn,hr⟩
  by_cases hb : n ≤ 10038
  · have hmin : 0 < n → n ≤ 10038 → witness (maskCount n) ≤ n :=
      of_decide_eq_true (of_checkBlocks allEarliest (n:=n) (by omega))
    simpa only [maskCount_eq hb, hr] using hmin hn hb
  · omega

#print axioms exact_first_occurrences

end SquarefreeCounts

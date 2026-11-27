import Mathlib

/-!
# Positive square plus squarefree representations

For each of the 101 levels printed in OEIS A085264, a positive integer at
most 10038 has exactly that many representations. The nine values
listed in A085266 are exactly the single-representation integers through
1024. These are finite certificates for the two conjectures.

Source: https://oeis.org/A085264 and https://oeis.org/A085266.
Proof and computation developed by Codex for @dwilfand-sys. The five
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

end SquarefreeCounts

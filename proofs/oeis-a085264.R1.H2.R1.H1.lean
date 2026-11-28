import OMAReductions.R_oeis_a085264_R1_H2_R1
import Mathlib

/-!
Ten uniform bounds for the 101-representation cutoff of A085264.
Source: https://oeis.org/A085264
Credit: @dwilfand-sys
The first three intervals use 27 odd prime count certificates. Seven later intervals follow
from the dyadic binomial bound. All 1,457 admissible profiles reserve 100 units.
-/

open scoped BigOperators

namespace A085265.DyadicPrimeCount

open Finset

def oddPrimesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun p => 2 < p ∧ p.Prime)

def oddPrimeCount (x : ℕ) : ℕ := (oddPrimesUpTo x).card

private lemma mem_oddPrimesUpTo {p x : ℕ} :
    p ∈ oddPrimesUpTo x ↔ p ≤ x ∧ 2 < p ∧ p.Prime := by
  simp [oddPrimesUpTo, Nat.lt_succ_iff]

/-- The primes newly counted between m and x divide the single binomial (x choose m). -/
theorem interval (m x e : ℕ) (hmx : m ≤ x) (hxm : x ≤ 2 * m)
    (he : 0 < e) (hpow : 2^e ≤ m + 1) :
    oddPrimeCount x ≤ oddPrimeCount m + x / e := by
  let T := oddPrimesUpTo x \ oddPrimesUpTo m
  have sub : oddPrimesUpTo m ⊆ oddPrimesUpTo x := by
    intro p hp
    obtain ⟨hpm, ho, hpr⟩ := mem_oddPrimesUpTo.mp hp
    exact mem_oddPrimesUpTo.mpr ⟨hpm.trans hmx, ho, hpr⟩
  have props {p : ℕ} (hp : p ∈ T) : m < p ∧ p ≤ x ∧ p.Prime := by
    obtain ⟨hx, hm⟩ := mem_sdiff.mp hp
    obtain ⟨hpx, ho, hpr⟩ := mem_oddPrimesUpTo.mp hx
    have hmp : m < p := by
      by_contra! h
      exact hm (mem_oddPrimesUpTo.mpr ⟨h, ho, hpr⟩)
    exact ⟨hmp, hpx, hpr⟩
  have hprod : (∏ p ∈ T, p) ∣ x.choose m := by
    apply Finset.prod_primes_dvd
    · exact fun p hp => (props hp).2.2.prime
    · intro p hp
      obtain ⟨hmp, hpx, hpr⟩ := props hp
      exact hpr.dvd_choose hmp (by omega) hpx
  have bound : (2 : ℕ) ^ (e * T.card) ≤ 2 ^ x := calc
    2 ^ (e * T.card) = ∏ _p ∈ T, 2 ^ e := by rw [pow_mul, prod_const]
    _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' fun _p hp => hpow.trans (props hp).1
    _ ≤ x.choose m := Nat.le_of_dvd (Nat.choose_pos hmx) hprod
    _ ≤ 2 ^ x := Nat.choose_le_two_pow x m
  have hd : T.card ≤ x / e := by
    apply (Nat.le_div_iff_mul_le he).mpr
    simpa only [Nat.mul_comm] using (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound
  have hcard : T.card + oddPrimeCount m = oddPrimeCount x :=
    card_sdiff_add_card_eq_card sub
  omega

theorem double (m e : ℕ) (he : 0 < e) (hpow : 2 ^ e ≤ m + 1) :
    oddPrimeCount (2*m) ≤ oddPrimeCount m + 2*m/e :=
  interval m (2*m) e (by omega) le_rfl he hpow

end A085265.DyadicPrimeCount

/- Factor certificates for 27 A085264 seed endpoints, Codex for @dwilfand-sys. Each seven-bit digit designates a proper divisor of a composite, or leaves the integer counted. This certificate proves the upper bounds required by the ten density bands. -/

namespace A085264.PrimeSeeds

open A085265.DyadicPrimeCount
open Finset

private def smallPrimeMark (v : ℕ) : ℕ := if 2 < v ∧ v.Prime then 1 else 0

private def smallPrimeSegment (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => smallPrimeSegment a h + smallPrimeMark (a+1+h)

private theorem smallPrimeCount_sum (a : ℕ) :
    oddPrimeCount a = ∑ i ∈ range (a+1), smallPrimeMark i := by
  simpa only [oddPrimeCount, oddPrimesUpTo, smallPrimeMark, Nat.cast_id] using
    (Finset.sum_boole (R := ℕ) (fun p : ℕ => 2 < p ∧ p.Prime) (range (a+1))).symm

private theorem smallPrimeSegment_sum (a h : ℕ) :
    (∑ i ∈ range h, smallPrimeMark (a+1+i)) = smallPrimeSegment a h := by
  induction h with
  | zero => simp [smallPrimeSegment]
  | succ h ih => rw [Finset.sum_range_succ, ih, smallPrimeSegment]

private def candidateMark (n d : ℕ) : ℕ :=
  if n ≤ 2 ∨ (1 < d ∧ d < n ∧ n % d = 0) then 0 else 1

private theorem smallPrimeMark_le_candidateMark (n d : ℕ) :
    smallPrimeMark n ≤ candidateMark n d := by
  by_cases hn : 2 < n ∧ n.Prime
  · have hkeep : ¬(n ≤ 2 ∨ (1 < d ∧ d < n ∧ n % d = 0)) := by
      rcases hn with ⟨hn,hpr⟩
      rintro (h | ⟨hd,hs,hm⟩)
      · omega
      · rcases (Nat.dvd_prime hpr).mp (Nat.dvd_of_mod_eq_zero hm) with h | h <;> omega
    simp [smallPrimeMark, candidateMark, hn, hkeep]
  · simp [smallPrimeMark, hn]

private def candidateSegment (a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | h+1, q => candidateSegment a h (q/128) + candidateMark (a+1+h) (q%128)

private theorem smallPrimeSegment_le_candidates (a h q : ℕ) :
    smallPrimeSegment a h ≤ candidateSegment a h q := by
  induction h generalizing q with
  | zero => exact Nat.le_refl 0
  | succ h ih =>
    exact Nat.add_le_add (ih (q/128)) (smallPrimeMark_le_candidateMark (a+1+h) (q%128))

private theorem smallPrimeAdvanceUpper (a h c d q : ℕ)
    (ha : oddPrimeCount a ≤ c) (hd : candidateSegment a h q = d) :
    oddPrimeCount (a+h) ≤ c+d := by
  have split : oddPrimeCount (a+h) = oddPrimeCount a + smallPrimeSegment a h := by
    rw [smallPrimeCount_sum (a+h), smallPrimeCount_sum a,
      show a+h+1 = a+1+h by omega, Finset.sum_range_add, smallPrimeSegment_sum]
  rw [split]
  exact Nat.add_le_add ha ((smallPrimeSegment_le_candidates a h q).trans_eq hd)

private theorem smallCountTo0 : oddPrimeCount 0 ≤ 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem smallCountTo64 : oddPrimeCount 64 ≤ 17 :=
  smallPrimeAdvanceUpper 0 64 0 17 0x2000800206080020008182000800206080020a08182000800206082820008182000800206080020e08182000828206080020008182
    smallCountTo0 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo128 : oddPrimeCount 128 ≤ 30 :=
  smallPrimeAdvanceUpper 64 64 17 13 0xa08002060800200081820e0800206080020a081820008382060828200081820008002060800200081820008282060838216081820a08002
    smallCountTo64 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo192 : oddPrimeCount 192 ≤ 42 :=
  smallPrimeAdvanceUpper 128 64 30 12 0x6080020e08182000800206085820a081820008002060828200081820e0800206080021a081820008282060800200081820a085820608002
    smallCountTo128 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo256 : oddPrimeCount 256 ≤ 53 :=
  smallPrimeAdvanceUpper 192 64 42 11 0x8182000800206083820a08182160800206082820e081821a08002060800200081820008282060800200081820a0868206080021608182
    smallCountTo192 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo320 : oddPrimeCount 320 ≤ 65 :=
  smallPrimeAdvanceUpper 256 64 53 12 0x838206080020a08182000800206082820008182000800206083822208182000828206086820e081820a08002060800200081820008582
    smallCountTo256 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo384 : oddPrimeCount 384 ≤ 75 :=
  smallPrimeAdvanceUpper 320 64 65 10 0x6088820a081820e08002060828200081821608382060800200081820008282060800226081820a08002060838200081821a080020608002
    smallCountTo320 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo448 : oddPrimeCount 448 ≤ 85 :=
  smallPrimeAdvanceUpper 384 64 75 10 0xa081820008882060828200081820008682060858200081820e08282060800200081820a0838206080020008182260800206080020a08182
    smallCountTo384 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo512 : oddPrimeCount 512 ≤ 96 :=
  smallPrimeAdvanceUpper 448 64 85 11 0x858206082820008182000800206080020e08182160828206080021a081820a08002060800222081820e0800206080020a081820008382
    smallCountTo448 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo576 : oddPrimeCount 576 ≤ 104 :=
  smallPrimeAdvanceUpper 512 64 96 8 0x6082821608182000800206088822e081821a08282060838200081820a0800206089820e08182000868206080020a0818200080020608282
    smallCountTo512 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo640 : oddPrimeCount 640 ≤ 114 :=
  smallPrimeAdvanceUpper 576 64 104 10 0x81820e08582060800226081820008282060800200081820a0800206086820008182000800206083820a08182220800206082820e08182
    smallCountTo576 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo704 : oddPrimeCount 704 ≤ 125 :=
  smallPrimeAdvanceUpper 640 64 114 11 0x8002060800216081820008282060800200081820a08b8206085820008182000838206080020a081821a08002060828222081820008982
    smallCountTo640 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo768 : oddPrimeCount 768 ≤ 134 :=
  smallPrimeAdvanceUpper 704 64 125 9 0x60838200081822e0828206080020e081820a0800206088820008182160800206080020a081820e080020608282000818200083820608682
    smallCountTo704 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo832 : oddPrimeCount 832 ≤ 144 :=
  smallPrimeAdvanceUpper 768 64 134 10 0x81820008282060898216081820a0800206083821a08182000888206085820a08182000800206082822608182000800206080020008182
    smallCountTo768 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo896 : oddPrimeCount 896 ≤ 153 :=
  smallPrimeAdvanceUpper 832 64 144 9 0xe0828206080023a081820a083820608b820008182000800206080020a08182160868206082820008182000800206080020e081822608282
    smallCountTo832 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo960 : oddPrimeCount 960 ≤ 161 :=
  smallPrimeAdvanceUpper 896 64 153 8 0x608e8222081820a08002060800216081820e0800206086820a081820008382060828200081820008b8206080021a0818200082820608382
    smallCountTo896 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1024 : oddPrimeCount 1024 ≤ 171 :=
  smallPrimeAdvanceUpper 960 64 161 10 0x3e081820a0800206080020e08182000858206080020a081822e08002060828200081820e0888206089820008182000828206080020008182
    smallCountTo960 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1088 : oddPrimeCount 1088 ≤ 180 :=
  smallPrimeAdvanceUpper 1024 64 171 9 0xa0868206080020008182220800206083820a08182000800206082820e081820008002060858200081823a0828206086822e081820a08002
    smallCountTo1024 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1152 : oddPrimeCount 1152 ≤ 189 :=
  smallPrimeAdvanceUpper 1088 64 180 9 0x6080020008182000838206080020a08182000858206082820008182260800206083820008182160828206088820e081820a08f820608002
    smallCountTo1088 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1216 : oddPrimeCount 1216 ≤ 197 :=
  smallPrimeAdvanceUpper 1152 64 189 8 0x81821a0898206080020a081820e0800206082821608182000838206080023a081820008282060858200081820a0888206083820008182
    smallCountTo1152 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1280 : oddPrimeCount 1280 ≤ 206 :=
  smallPrimeAdvanceUpper 1216 64 197 9 0x8b8206080020a0818200080020608282000818222085820608e8200081820e0828206080021a081820a083820608f8226081820008002
    smallCountTo1216 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1344 : oddPrimeCount 1344 ≤ 216 :=
  smallPrimeAdvanceUpper 1280 64 206 10 0x6080020a08182000800206082820008182000800206080020e081821a08282060800200081820a0800206085823e081820e086820608882
    smallCountTo1280 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1408 : oddPrimeCount 1408 ≤ 221 :=
  smallPrimeAdvanceUpper 1344 64 216 5 0xa08182260838206082822e081820008e8206080024a081820008282060838200081820a0898206086820e0818216080020608b820a08182
    smallCountTo1344 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1472 : oddPrimeCount 1472 ≤ 232 :=
  smallPrimeAdvanceUpper 1408 64 221 11 0x888206082821a081820e08002060800200081820008282060800216081820a08002060800200081823e0800206083820a081821a08002
    smallCountTo1408 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1536 : oddPrimeCount 1536 ≤ 241 :=
  smallPrimeAdvanceUpper 1472 64 232 9 0x6082820e081820008002060800200081820008282060800226081820a08582060800222081824a0838206080020a0818216080020608282
    smallCountTo1472 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1600 : oddPrimeCount 1600 ≤ 250 :=
  smallPrimeAdvanceUpper 1536 64 241 9 0x3a081822e0800206083820008182000828206080020e081820a0800206080021608182260800206080020a081820e0928206082820008182
    smallCountTo1536 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1664 : oddPrimeCount 1664 ≤ 260 :=
  smallPrimeAdvanceUpper 1600 64 250 10 0x8382060800200081820008282060800200081820a0800206083822e0818200085820608f820a081822208682060828200081821608002
    smallCountTo1600 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1728 : oddPrimeCount 1728 ≤ 268 :=
  smallPrimeAdvanceUpper 1664 64 260 8 0x60800200081820e082820608b8252081820a0838206089820008182000800206086820a081820008e820608282220818200080020608582
    smallCountTo1664 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1792 : oddPrimeCount 1792 ≤ 277 :=
  smallPrimeAdvanceUpper 1728 64 268 9 0xe081820008282060928200081820a08002060888200081820e0800206094820a081823a08382060828200081821a0800206080020008182
    smallCountTo1728 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1856 : oddPrimeCount 1856 ≤ 282 :=
  smallPrimeAdvanceUpper 1792 64 277 5 0x1608282060838200081820a0868206080020e081822e0888206080020a081823e08002060828216081820e08982060800256081822208282
    smallCountTo1792 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1920 : oddPrimeCount 1920 ≤ 292 :=
  smallPrimeAdvanceUpper 1856 64 282 10 0x60858200081820a0800206080020008182000800206083820a081820008f8206082820e08182000858206080022e0818200082820608982
    smallCountTo1856 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1984 : oddPrimeCount 1984 ≤ 298 :=
  smallPrimeAdvanceUpper 1920 64 292 6 0x22081820a09482060800200081821a083820608e820a081820008002060828226081824a0868206083821608182000828206080020e08182
    smallCountTo1920 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2048 : oddPrimeCount 2048 ≤ 308 :=
  smallPrimeAdvanceUpper 1984 64 298 10 0xa0800206085820008182000800206080020a081820e0800206082820008182560838206080020008182260828206080021a081820a08b82
    smallCountTo1984 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2112 : oddPrimeCount 2112 ≤ 317 :=
  smallPrimeAdvanceUpper 2048 64 308 9 0x60838200081821608e8206080020a08182000898206082823e081820008002060800200081820e08282060800216081820a083820608002
    smallCountTo2048 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2176 : oddPrimeCount 2176 ≤ 325 :=
  smallPrimeAdvanceUpper 2112 64 317 8 0x81823a0868206085820a08182000800206082820008182000800206089820e081820008282060888200081820a0858206086825208182
    smallCountTo2112 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2240 : oddPrimeCount 2240 ≤ 332 :=
  smallPrimeAdvanceUpper 2176 64 325 7 0xe0800206092820a08182160838206082821a081823e0800206080025e081820008282060838200081820a088820608b820e081820008002
    smallCountTo2176 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2304 : oddPrimeCount 2304 ≤ 341 :=
  smallPrimeAdvanceUpper 2240 64 332 9 0x6080020a081821a0800206082824a081820e08f82060800200081820008282060958200081820a080020608e82000818200085820608382
    smallCountTo2240 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2368 : oddPrimeCount 2368 ≤ 349 :=
  smallPrimeAdvanceUpper 2304 64 341 8 0xa08182000800206082820e081821608b82060868222081820008282060800200081820a0800206080021a08182000838206088820a08182
    smallCountTo2304 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2432 : oddPrimeCount 2432 ≤ 359 :=
  smallPrimeAdvanceUpper 2368 64 349 10 0x2e0800206082820008182000800206083820008182000828206080020e081820a08e8206080022608182000948206080020a081820e08582
    smallCountTo2368 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2496 : oddPrimeCount 2496 ≤ 366 :=
  smallPrimeAdvanceUpper 2432 64 359 7 0x6082820008182000838206080023e08182160828206080022e081820a0800206083820008182000928206086820a0818226097820608282
    smallCountTo2432 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2560 : oddPrimeCount 2560 ≤ 374 :=
  smallPrimeAdvanceUpper 2496 64 366 8 0x160818252080020608b821a081820e08282060858200081820a0838206080022208182560800206080020a08182000800206082820008182
    smallCountTo2496 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2624 : oddPrimeCount 2624 ≤ 380 :=
  smallPrimeAdvanceUpper 2560 64 374 6 0x1a0858206088820e081823e0828206080023a081820a08682060800200081820e08b8206089820a081820008382060828200081820009582
    smallCountTo2560 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2688 : oddPrimeCount 2688 ≤ 389 :=
  smallPrimeAdvanceUpper 2624 64 380 9 0x60928216081820008282060838226081820a0800206085820e08182000800206080020a081822208002060828200081820e080020608002
    smallCountTo2624 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2752 : oddPrimeCount 2752 ≤ 400 :=
  smallPrimeAdvanceUpper 2688 64 389 11 0x8182000828206080024a081820a0800206080020008182160800206083820a08182000800206082820e08182000868206094820008182
    smallCountTo2688 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2816 : oddPrimeCount 2816 ≤ 408 :=
  smallPrimeAdvanceUpper 2752 64 400 8 0x82820608f8216081820a0800206088825e08182000838206085820a08182000800206082820008182000800206083826a081823a08282
    smallCountTo2752 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2880 : oddPrimeCount 2880 ≤ 416 :=
  smallPrimeAdvanceUpper 2816 64 408 8 0x6080020e081820a0858206089820008182000888206080020a081820e08002060828200081820008382060978226081821a082820608002
    smallCountTo2816 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2944 : oddPrimeCount 2944 ≤ 423 :=
  smallPrimeAdvanceUpper 2880 64 416 7 0x56081820a0800206083821608182000868206080020a081820009482060828200081822e0928206080023a081820e0828206080022208182
    smallCountTo2880 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3008 : oddPrimeCount 3008 ≤ 430 :=
  smallPrimeAdvanceUpper 2944 64 423 7 0xa0838206086820008182000858206080020a08182000800206082821a0818216089820608e820e081825208282060800200081820a08f82
    smallCountTo2944 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3072 : oddPrimeCount 3072 ≤ 438 :=
  smallPrimeAdvanceUpper 3008 64 430 8 0x6080022e081820e0800206080020a081821a08382060828200081820008882060858200081825608282060838200081820a080020609282
    smallCountTo3008 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3136 : oddPrimeCount 3136 ≤ 444 :=
  smallPrimeAdvanceUpper 3072 64 438 6 0xe08182220800206080020a081820008582060828226081820e08e82060868200081821608282060800200081820a09a820608f821a08182
    smallCountTo3072 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3200 : oddPrimeCount 3200 ≤ 451 :=
  smallPrimeAdvanceUpper 3136 64 444 7 0x958206083820a081825e08b8206082820e081823a08002060800200081822608282060858200081820a0800206080023e081822e08382
    smallCountTo3136 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3264 : oddPrimeCount 3264 ≤ 460 :=
  smallPrimeAdvanceUpper 3200 64 451 9 0x6080020a081820008682060828200081820008582060838200081826a0828206094820e081820a088820608002000818200080020608682
    smallCountTo3200 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3328 : oddPrimeCount 3328 ≤ 467 :=
  smallPrimeAdvanceUpper 3264 64 460 7 0xa081820e0800206082823a081822208382060898216081824a08282060800200081820a08002060838200081823e0800206080020a08182
    smallCountTo3264 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3359 : oddPrimeCount 3359 ≤ 472 :=
  smallPrimeAdvanceUpper 3328 31 467 5 0x100040c10504bc1030434100040c1000444103041c105040c100
    smallCountTo3328 (by decide +kernel)

theorem base_3359 : oddPrimeCount 3359 ≤ 472 := smallCountTo3359

set_option maxRecDepth 10000 in
private theorem smallCountTo3423 : oddPrimeCount 3423 ≤ 479 :=
  smallPrimeAdvanceUpper 3359 64 472 7 0x4001030414107040c1000400103042c11f040c11104141030400100040c10504ac103044c129040c100041c1030400105040c10d042c103
    smallCountTo3359 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3487 : oddPrimeCount 3487 ≤ 486 :=
  smallPrimeAdvanceUpper 3423 64 479 7 0x414117040c12f0400103041c113040c10b04141030400107040c10504001030400100040c1000400103045c105040c10704ec103041410b
    smallCountTo3423 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3545 : oddPrimeCount 3545 ≤ 495 :=
  smallPrimeAdvanceUpper 3487 58 486 9 0x1030400107040c10d0400103047c105040c10b04001030414100040c10704341030400100040c10004141030400100040c105
    smallCountTo3487 (by decide +kernel)

theorem base_3545 : oddPrimeCount 3545 ≤ 495 := smallCountTo3545

set_option maxRecDepth 10000 in
private theorem smallCountTo3609 : oddPrimeCount 3609 ≤ 503 :=
  smallPrimeAdvanceUpper 3545 64 495 8 0x40010304d410b040c1000400103041c105040c12b04001030414107040c10004001030444125040c100041410304ec10d040c1050400103
    smallCountTo3545 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3673 : oddPrimeCount 3673 ≤ 512 :=
  smallPrimeAdvanceUpper 3609 64 503 9 0x45c100040c100041c1030400105040c11304001030414100040c10b0400103041c129040c10d04141030400107040c105044c1030400100
    smallCountTo3609 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3737 : oddPrimeCount 3737 ≤ 520 :=
  smallPrimeAdvanceUpper 3673 64 512 8 0x40c10004341030474105040c10704001030414100040c100041c103042c100040c12f0414103040013d040c1050400103041c100040c125
    smallCountTo3673 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3767 : oddPrimeCount 3767 ≤ 523 :=
  smallPrimeAdvanceUpper 3737 30 520 3 0x100040c1130414103045c10b040c10504341030400135040c100
    smallCountTo3737 (by decide +kernel)

theorem base_3767 : oddPrimeCount 3767 ≤ 523 := smallCountTo3767

set_option maxRecDepth 10000 in
private theorem smallCountTo3831 : oddPrimeCount 3831 ≤ 530 :=
  smallPrimeAdvanceUpper 3767 64 523 7 0x400103041c105040c100044c1030414107040c1110400103040011d040c10004141030434125040c105042c1030400100040c12b041c103
    smallCountTo3767 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3895 : oddPrimeCount 3895 ≤ 538 :=
  smallPrimeAdvanceUpper 3831 64 530 8 0x400105040c10b045c1030414100040c1000400103041c111040c100041410304d4107040c1050400103040010b040c10d04001030444105
    smallCountTo3831 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3959 : oddPrimeCount 3959 ≤ 547 :=
  smallPrimeAdvanceUpper 3895 64 538 9 0x40c10704bc1030414100040c100041c1030400100040c10004141030400100040c105047c103041c100040c100042c10304ec105040c125
    smallCountTo3895 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4023 : oddPrimeCount 4023 ≤ 555 :=
  smallPrimeAdvanceUpper 3959 64 547 8 0x4441030414100040c10b047410304a4117040c1070414103040010d040c105041c1030400100040c100044c1030400105040c1000400103
    smallCountTo3959 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4025 : oddPrimeCount 4025 ≤ 555 :=
  smallPrimeAdvanceUpper 4023 2 555 0 0x105
    smallCountTo4023 (by decide +kernel)

theorem base_4025 : oddPrimeCount 4025 ≤ 555 := smallCountTo4025

set_option maxRecDepth 10000 in
private theorem smallCountTo4089 : oddPrimeCount 4089 ≤ 561 :=
  smallPrimeAdvanceUpper 4025 64 555 6 0x4001030474125040c10b041c1030434105040c10004001030414100040c11f0444103041c10d040c10004141030400107040c10504f4103
    smallCountTo4025 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4095 : oddPrimeCount 4095 ≤ 563 :=
  smallPrimeAdvanceUpper 4089 6 561 2 0x1000400103
    smallCountTo4089 (by decide +kernel)

theorem base_4095 : oddPrimeCount 4095 ≤ 563 := smallCountTo4095

set_option maxRecDepth 10000 in
private theorem smallCountTo4151 : oddPrimeCount 4151 ≤ 569 :=
  smallPrimeAdvanceUpper 4095 56 563 6 0x444100040c10b0414103041c100040c105045c1030434107040c10004001030400105040c10004a4103041410b040c107
    smallCountTo4095 (by decide +kernel)

theorem base_4151 : oddPrimeCount 4151 ≤ 569 := smallCountTo4151

set_option maxRecDepth 10000 in
private theorem smallCountTo4215 : oddPrimeCount 4215 ≤ 575 :=
  smallPrimeAdvanceUpper 4151 64 569 6 0x4001030400100040c1170414103042c12b040c1050400103049412f040c13504ec103041c105040c10d04001030414107040c100042c103
    smallCountTo4151 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4227 : oddPrimeCount 4227 ≤ 577 :=
  smallPrimeAdvanceUpper 4215 12 575 2 0x400100040c1290414103
    smallCountTo4215 (by decide +kernel)

theorem base_4227 : oddPrimeCount 4227 ≤ 577 := smallCountTo4227

set_option maxRecDepth 10000 in
private theorem smallCountTo4287 : oddPrimeCount 4287 ≤ 587 :=
  smallPrimeAdvanceUpper 4227 60 577 10 0x400100040c105044c1030400100040c11f041c1030400105040c10004001030414111040c1000400103041c10b040c1000414103
    smallCountTo4227 (by decide +kernel)

theorem base_4287 : oddPrimeCount 4287 ≤ 587 := smallCountTo4287

set_option maxRecDepth 10000 in
private theorem smallCountTo4351 : oddPrimeCount 4351 ≤ 593 :=
  smallPrimeAdvanceUpper 4287 64 587 6 0x400107040c1050400103042c10d040c13b047c103044c105040c10704741030414100040c13d041c1030400100040c12b04141030400113
    smallCountTo4287 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4389 : oddPrimeCount 4389 ≤ 596 :=
  smallPrimeAdvanceUpper 4351 38 593 3 0x1030414100040c1070400103042c111040c1000414103047410d040c10504a4103
    smallCountTo4351 (by decide +kernel)

theorem base_4389 : oddPrimeCount 4389 ≤ 596 := smallCountTo4389

set_option maxRecDepth 10000 in
private theorem smallCountTo4453 : oddPrimeCount 4453 ≤ 604 :=
  smallPrimeAdvanceUpper 4389 64 596 8 0x400117040c10004d4103041c105040c100042c1030414107040c1000400103044c12b040c10b0414103045c100040c1050400103040013d
    smallCountTo4389 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4511 : oddPrimeCount 4511 ≤ 610 :=
  smallPrimeAdvanceUpper 4453 58 604 6 0x1030400107040c100041410304a4111040c105042c1030400100040c107050c1030400105040c10b041c1030414100040c10d
    smallCountTo4453 (by decide +kernel)

theorem base_4511 : oddPrimeCount 4511 ≤ 610 := smallCountTo4511

set_option maxRecDepth 10000 in
private theorem smallCountTo4575 : oddPrimeCount 4575 ≤ 618 :=
  smallPrimeAdvanceUpper 4511 64 610 8 0x4001030400100040c1000414103041c117040c1050434103044c107040c10004001030474105040c12f04001030414100040c1070444103
    smallCountTo4511 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4639 : oddPrimeCount 4639 ≤ 625 :=
  smallPrimeAdvanceUpper 4575 64 618 7 0x45c113040c10004141030434100040c105040010304ac100040c111042c103041c105040c11f04001030414107040c10b04a41030400100
    smallCountTo4575 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4649 : oddPrimeCount 4649 ≤ 627 :=
  smallPrimeAdvanceUpper 4639 10 625 2 0x1030400105040c100
    smallCountTo4639 (by decide +kernel)

theorem base_4649 : oddPrimeCount 4649 ≤ 627 := smallCountTo4649

set_option maxRecDepth 10000 in
private theorem smallCountTo4713 : oddPrimeCount 4713 ≤ 634 :=
  smallPrimeAdvanceUpper 4649 64 627 7 0x4001030414100040c13b04001030434107040c1000414103040011f040c10504ac103040010d040c10704941030400105040c111041c103
    smallCountTo4649 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4777 : oddPrimeCount 4777 ≤ 640 :=
  smallPrimeAdvanceUpper 4713 64 634 6 0x414135040c10004001030474100040c1000414103041c10b040c10504bc1030400107040c1430400103042c105040c11304341030414111
    smallCountTo4713 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4811 : oddPrimeCount 4811 ≤ 646 :=
  smallPrimeAdvanceUpper 4777 34 640 6 0x103041c100040c10004001030400105040c1000400103041410b040c111
    smallCountTo4777 (by decide +kernel)

theorem base_4811 : oddPrimeCount 4811 ≤ 646 := smallCountTo4811

set_option maxRecDepth 10000 in
private theorem smallCountTo4875 : oddPrimeCount 4875 ≤ 651 :=
  smallPrimeAdvanceUpper 4811 64 646 5 0x400103040013d040c1070414103042c100040c105041c10304bc11d040c1250434103045c105040c12b0400103041411f040c100042c103
    smallCountTo4811 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4939 : oddPrimeCount 4939 ≤ 659 :=
  smallPrimeAdvanceUpper 4875 64 651 8 0x400107040c11304141030400143040c10504ec1030434100040c10704001030444105040c100041c103041410d040c1000400103040010b
    smallCountTo4875 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5001 : oddPrimeCount 5001 ≤ 668 :=
  smallPrimeAdvanceUpper 4939 62 659 9 0x1030400105040c10704001030414100040c10b041c1030400100040c10004141030434111040c1050400103041c100040c1130400103
    smallCountTo4939 (by decide +kernel)

theorem base_5001 : oddPrimeCount 5001 ≤ 668 := smallCountTo5001

set_option maxRecDepth 10000 in
private theorem smallCountTo5065 : oddPrimeCount 5065 ≤ 676 :=
  smallPrimeAdvanceUpper 5001 64 668 8 0x400105040c1000400103041411d040c1000400103042c12f040c10704141030400147040c105041c103040011f040c10d040010304f4105
    smallCountTo5001 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5129 : oddPrimeCount 5129 ≤ 684 :=
  smallPrimeAdvanceUpper 5065 64 676 8 0x40c125042c1030414100040c10004341030400107040c10b04141030400100040c1050400103044c100040c107040010304bc105040c117
    smallCountTo5065 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5193 : oddPrimeCount 5193 ≤ 690 :=
  smallPrimeAdvanceUpper 5129 64 684 6 0x41c103041410b040c13504941030400113040c1000414103041c10d040c10504001030400107040c11f0400103051c105040c1000474103
    smallCountTo5129 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5235 : oddPrimeCount 5235 ≤ 695 :=
  smallPrimeAdvanceUpper 5193 42 690 5 0x1050400103041c10b040c12904001030434105040c111045c1030414100040c1000400103
    smallCountTo5193 (by decide +kernel)

theorem base_5235 : oddPrimeCount 5235 ≤ 695 := smallCountTo5235

set_option maxRecDepth 10000 in
private theorem smallCountTo5299 : oddPrimeCount 5299 ≤ 701 :=
  smallPrimeAdvanceUpper 5235 64 695 6 0x40010d040c1070414103047413b040c105041c1030400113040c117042c1030400105040c10004001030414111040c10b050c1030400107
    smallCountTo5235 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5363 : oddPrimeCount 5363 ≤ 707 :=
  smallPrimeAdvanceUpper 5299 64 701 6 0x40c1000414103040012f040c10504341030444100040c10705241030400105040c113041c1030414100040c10004d4103042c117040c11f
    smallCountTo5299 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5427 : oddPrimeCount 5427 ≤ 715 :=
  smallPrimeAdvanceUpper 5363 64 707 8 0x414103041c129040c105044c1030400107040c10004441030400105040c100042c1030414100040c10704001030400100040c10b0414103
    smallCountTo5363 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5491 : oddPrimeCount 5491 ≤ 724 :=
  smallPrimeAdvanceUpper 5427 64 715 9 0x4f4100040c10504001030400100040c10d0400103041c105040c13504ac1030414107040c10004341030400100040c1000414103042c111
    smallCountTo5427 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5517 : oddPrimeCount 5517 ≤ 727 :=
  smallPrimeAdvanceUpper 5491 26 724 3 0x1030414117040c10004001030400107040c1250414103
    smallCountTo5491 (by decide +kernel)

theorem base_5517 : oddPrimeCount 5517 ≤ 727 := smallCountTo5517

set_option maxRecDepth 10000 in
private theorem smallCountTo5581 : oddPrimeCount 5581 ≤ 736 :=
  smallPrimeAdvanceUpper 5517 64 727 9 0x400100040c1050400103040010b040c1070474103045c105040c11f041c1030414100040c1430400103044c100040c1000414103041c100
    smallCountTo5517 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5645 : oddPrimeCount 5645 ≤ 740 :=
  smallPrimeAdvanceUpper 5581 64 736 4 0x40c10504941030400107040c11d042c1030434105040c147047c1030414129040c1070400103044410d040c12b04141030400100040c105
    smallCountTo5581 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5709 : oddPrimeCount 5709 ≤ 750 :=
  smallPrimeAdvanceUpper 5645 64 740 10 0x4001030400100040c1000400103041c105040c10004d41030414107040c10d0400103042c100040c100041410304a4100040c1050434103
    smallCountTo5645 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5773 : oddPrimeCount 5773 ≤ 756 :=
  smallPrimeAdvanceUpper 5709 64 750 6 0x40011d040c100041c10304ec105040c111042c1030414100040c1000400103041c100040c10b04141030434107040c10505241030474117
    smallCountTo5709 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5837 : oddPrimeCount 5837 ≤ 764 :=
  smallPrimeAdvanceUpper 5773 64 756 8 0x40c13504001030400105040c1070400103041410b040c100041c1030400125040c1000414103042c100040c1050400103041c113040c10d
    smallCountTo5773 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5849 : oddPrimeCount 5849 ≤ 767 :=
  smallPrimeAdvanceUpper 5837 12 764 3 0x4001030400105040c100
    smallCountTo5837 (by decide +kernel)

theorem base_5849 : oddPrimeCount 5849 ≤ 767 := smallCountTo5849

set_option maxRecDepth 10000 in
private theorem smallCountTo5913 : oddPrimeCount 5913 ≤ 776 :=
  smallPrimeAdvanceUpper 5849 64 767 9 0x4001030414100040c100042c1030400100040c10704141030400100040c105041c10304ac147040c10004441030400105040c113045c103
    smallCountTo5849 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5977 : oddPrimeCount 5977 ≤ 780 :=
  smallPrimeAdvanceUpper 5913 64 776 4 0x41413d040c11f04001030400107040c1110414103040010d040c105044c103042c100040c10704ec103050c105040c12f041c103041412b
    smallCountTo5913 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6041 : oddPrimeCount 6041 ≤ 786 :=
  smallPrimeAdvanceUpper 5977 64 780 6 0x40c100047c1030400135040c10d0414103041c111040c10504001030400107040c10b0434103044c105040c10004941030414100040c107
    smallCountTo5977 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6105 : oddPrimeCount 6105 ≤ 795 :=
  smallPrimeAdvanceUpper 6041 64 786 9 0x4001030400117040c1000414103052410b040c10504001030434100040c13b0400103041c105040c10004001030414107040c1000444103
    smallCountTo6041 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6169 : oddPrimeCount 6169 ≤ 802 :=
  smallPrimeAdvanceUpper 6105 64 795 7 0x47c129040c10004141030474100040c105042c1030400100040c111041c1030400105040c10b0400103041412f040c13d0400103041c11f
    smallCountTo6105 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6233 : oddPrimeCount 6233 ≤ 810 :=
  smallPrimeAdvanceUpper 6169 64 802 8 0x40c10004141030494107040c105045c10304a410b040c10004001030400105040c10704001030414100040c100041c1030434100040c117
    smallCountTo6169 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6267 : oddPrimeCount 6267 ≤ 813 :=
  smallPrimeAdvanceUpper 6233 34 810 3 0x105040c111053c1030414100040c1070434103040010b040c1000414103
    smallCountTo6233 (by decide +kernel)

theorem base_6267 : oddPrimeCount 6267 ≤ 813 := smallCountTo6267

set_option maxRecDepth 10000 in
private theorem smallCountTo6331 : oddPrimeCount 6331 ≤ 823 :=
  smallPrimeAdvanceUpper 6267 64 813 10 0x400100040c1050400103042c13d040c100044c103041c105040c10004001030414107040c10004ec1030400147040c1000414103040010d
    smallCountTo6267 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6395 : oddPrimeCount 6395 ≤ 832 :=
  smallPrimeAdvanceUpper 6331 64 823 9 0x40c10504001030444100040c10b041c1030400105040c10004001030414100040c1170400103041c100040c10d04141030400107040c105
    smallCountTo6331 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6459 : oddPrimeCount 6459 ≤ 837 :=
  smallPrimeAdvanceUpper 6395 64 832 5 0x4001030494113040c12b0434103042c105040c10704001030414100040c13b041c10304a412f040c11104141030400100040c105042c103
    smallCountTo6395 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6523 : oddPrimeCount 6523 ≤ 842 :=
  smallPrimeAdvanceUpper 6459 64 837 5 0x41c117040c11d04001030400105040c10b0400103041410d040c10004ac1030524143040c1070414103045c111040c105041c103040010b
    smallCountTo6459 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6587 : oddPrimeCount 6587 ≤ 851 :=
  smallPrimeAdvanceUpper 6523 64 842 9 0x40c13d040010304bc105040c10d047c1030414100040c1000400103053c107040c10004141030400100040c1050400103040011d040c107
    smallCountTo6523 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6651 : oddPrimeCount 6651 ≤ 855 :=
  smallPrimeAdvanceUpper 6587 64 851 4 0x42c103044c105040c100041c1030414100040c10b04441030434100040c1250414103041c113040c10504001030474107040c11104f4103
    smallCountTo6587 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6715 : oddPrimeCount 6715 ≤ 865 :=
  smallPrimeAdvanceUpper 6651 64 855 10 0x400105040c1000400103041413b040c1070400103042c100040c12904141030400100040c10504941030400100040c1130400103041c105
    smallCountTo6651 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6779 : oddPrimeCount 6779 ≤ 871 :=
  smallPrimeAdvanceUpper 6715 64 865 6 0x40c100042c1030414107040c13504001030400117040c10b0414103044412b040c10504741030400100040c143041c1030434105040c100
    smallCountTo6715 (by decide +kernel)

theorem base_6779 : oddPrimeCount 6779 ≤ 871 := smallCountTo6779

set_option maxRecDepth 10000 in
private theorem smallCountTo6843 : oddPrimeCount 6843 ≤ 880 :=
  smallPrimeAdvanceUpper 6779 64 871 9 0x400103041410b040c1000400103041c10d040c1000414103042c107040c1050444103044c100040c10004001030400105040c1070400103
    smallCountTo6779 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6907 : oddPrimeCount 6907 ≤ 887 :=
  smallPrimeAdvanceUpper 6843 64 880 7 0x414129040c10d041c1030400113040c10004141030400100040c1050434103041c100040c147054c10304f4105040c100050c1030414100
    smallCountTo6843 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6971 : oddPrimeCount 6971 ≤ 895 :=
  smallPrimeAdvanceUpper 6907 64 887 8 0x40c100047c103040010b040c1070414103043411d040c105041c103042c135040c10004001030444105040c10004001030414100040c100
    smallCountTo6907 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7035 : oddPrimeCount 7035 ≤ 903 :=
  smallPrimeAdvanceUpper 6971 64 895 8 0x44c1030400107040c10004141030474100040c1050400103040012f040c10704ac1030400105040c100041c1030414100040c14f0434103
    smallCountTo6971 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7099 : oddPrimeCount 7099 ≤ 908 :=
  smallPrimeAdvanceUpper 7035 64 903 5 0x47c100040c1000414103041c10b040c1050400103045c107040c1250400103042c105040c10005241030414113040c10704a410304bc11f
    smallCountTo7035 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7163 : oddPrimeCount 7163 ≤ 915 :=
  smallPrimeAdvanceUpper 7099 64 908 7 0x40c1000414103040010d040c105042c1030400111040c1000400103041c105040c10b04941030414107040c100045c1030444100040c10d
    smallCountTo7099 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7227 : oddPrimeCount 7227 ≤ 922 :=
  smallPrimeAdvanceUpper 7163 64 915 7 0x414103050c147040c105040010304ac10b040c100041c1030400105040c117044c1030414100040c1000400103041c100040c11f0414103
    smallCountTo7163 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7291 : oddPrimeCount 7291 ≤ 928 :=
  smallPrimeAdvanceUpper 7227 64 922 6 0x400107040c10504001030434100040c100042c1030400105040c10704d4103041410d040c10b041c103044c11d040c10004141030494117
    smallCountTo7227 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7355 : oddPrimeCount 7355 ≤ 936 :=
  smallPrimeAdvanceUpper 7291 64 928 8 0x40c1050400103041c143040c1000400103051c105040c10d04001030414111040c1000400103042c129040c10704141030400100040c105
    smallCountTo7291 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7419 : oddPrimeCount 7419 ≤ 940 :=
  smallPrimeAdvanceUpper 7355 64 936 4 0x41c1030444125040c13504001030524105040c12f042c1030414153040c11304001030434107040c10b0414103047c100040c1050400103
    smallCountTo7355 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7455 : oddPrimeCount 7455 ≤ 942 :=
  smallPrimeAdvanceUpper 7419 36 940 2 0x4a410d040c10704441030400105040c12b041c103041410b040c1000474103
    smallCountTo7419 (by decide +kernel)

theorem base_7455 : oddPrimeCount 7455 ≤ 942 := smallCountTo7455

set_option maxRecDepth 10000 in
private theorem smallCountTo7519 : oddPrimeCount 7519 ≤ 951 :=
  smallPrimeAdvanceUpper 7455 64 942 9 0x400100040c1110414103041c11f040c10504001030400107040c100040010304ec105040c10004341030414100040c107042c1030400149
    smallCountTo7455 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7583 : oddPrimeCount 7583 ≤ 962 :=
  smallPrimeAdvanceUpper 7519 64 951 11 0x40c10004141030400111040c10504001030400113040c1000400103041c105040c10004001030414107040c1430400103040010b040c100
    smallCountTo7519 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7647 : oddPrimeCount 7647 ≤ 969 :=
  smallPrimeAdvanceUpper 7583 64 962 7 0x4141030400100040c105051c103042c100040c100041c103045c105040c1130400103041411d040c10d0444103041c100040c1000414103
    smallCountTo7583 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7711 : oddPrimeCount 7711 ≤ 977 :=
  smallPrimeAdvanceUpper 7647 64 969 8 0x400107040c105043410304bc14f040c10b04001030400105040c10704001030414100040c100041c10304ac100040c1000414103043410b
    smallCountTo7647 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7775 : oddPrimeCount 7775 ≤ 984 :=
  smallPrimeAdvanceUpper 7711 64 977 7 0x40c1050400103041c100040c10004ec103042c105040c1470400103041413d040c11704001030400100040c10704141030444113040c105
    smallCountTo7711 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7839 : oddPrimeCount 7839 ≤ 989 :=
  smallPrimeAdvanceUpper 7775 64 984 5 0x41c103047c12b040c10d04001030400105040c10b04741030414125040c14904341030400107040c10004141030400129040c1050444103
    smallCountTo7775 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7903 : oddPrimeCount 7903 ≤ 997 :=
  smallPrimeAdvanceUpper 7839 64 989 8 0x40010b040c10704bc1030400105040c11d041c1030414100040c11104001030400100040c1000414103041c10d040c10504d41030400107
    smallCountTo7839 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7967 : oddPrimeCount 7967 ≤ 1005 :=
  smallPrimeAdvanceUpper 7903 64 997 8 0x40c100042c10304a4105040c10005641030414100040c10704001030400111040c10d04141030400100040c1050524103044c100040c11f
    smallCountTo7903 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8031 : oddPrimeCount 8031 ≤ 1009 :=
  smallPrimeAdvanceUpper 7967 64 1005 4 0x434103041c105040c14f045c1030414107040c13d0400103042c113040c13504141030400100040c10504001030434147040c117041c103
    smallCountTo7967 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8095 : oddPrimeCount 8095 ≤ 1017 :=
  smallPrimeAdvanceUpper 8031 64 1009 8 0x474105040c100042c103041410d040c1530400103041c100040c10b04141030400107040c10504a4103040013b040c10004001030400105
    smallCountTo8031 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8159 : oddPrimeCount 8159 ≤ 1022 :=
  smallPrimeAdvanceUpper 8095 64 1017 5 0x40c1070400103041410b040c100041c1030400117040c1000414103042c12f040c105053c103041c111040c1000474103047c105040c129
    smallCountTo8095 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8191 : oddPrimeCount 8191 ≤ 1027 :=
  smallPrimeAdvanceUpper 8159 32 1022 5 0x4001030414100040c100042c1030434100040c1070414103044c100
    smallCountTo8159 (by decide +kernel)

theorem base_8191 : oddPrimeCount 8191 ≤ 1027 := smallCountTo8191

set_option maxRecDepth 10000 in
private theorem smallCountTo8255 : oddPrimeCount 8255 ≤ 1034 :=
  smallPrimeAdvanceUpper 8191 64 1027 7 0x40c105041c10304ec10d040c11d040010304ac105040c10004001030414113040c10004001030400107040c10004141030524125040c105
    smallCountTo8191 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8319 : oddPrimeCount 8319 ≤ 1043 :=
  smallPrimeAdvanceUpper 8255 64 1034 9 0x45c103042c100040c10704001030400105040c111041c1030414100040c1000400103040012b040c1130414103041c100040c1050400103
    smallCountTo8255 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8383 : oddPrimeCount 8383 ≤ 1048 :=
  smallPrimeAdvanceUpper 8319 64 1043 5 0x4d4107040c10b04001030434105040c11f044c1030414111040c107040010304f410d040c1000414103040010b040c10504001030444153
    smallCountTo8319 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8447 : oddPrimeCount 8447 ≤ 1056 :=
  smallPrimeAdvanceUpper 8383 64 1048 8 0x40c1000400103041c105040c125047c1030414107040c10d04bc103044c100040c10004141030400100040c105042c103045c100040c100
    smallCountTo8383 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8511 : oddPrimeCount 8511 ≤ 1059 :=
  smallPrimeAdvanceUpper 8447 64 1056 3 0x41c103053c105040c10b04001030414100040c12b0494103041c13d040c11104141030434107040c1050474103040010b040c12f050c103
    smallCountTo8447 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8575 : oddPrimeCount 8575 ≤ 1067 :=
  smallPrimeAdvanceUpper 8511 64 1059 8 0x400105040c10704001030414100040c113041c1030400100040c1000414103054c111040c10504ac103041c100040c10d042c1030400105
    smallCountTo8511 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8639 : oddPrimeCount 8639 ≤ 1074 :=
  smallPrimeAdvanceUpper 8575 64 1067 7 0x40c1170400103041411f040c10b04341030400100040c1070414103040014f040c105041c1030494100040c10004001030564105040c135
    smallCountTo8575 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8703 : oddPrimeCount 8703 ≤ 1083 :=
  smallPrimeAdvanceUpper 8639 64 1074 9 0x4001030414100040c1290444103042c107040c1000414103040010d040c10504001030400113040c10704001030400105040c100041c103
    smallCountTo8639 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8767 : oddPrimeCount 8767 ≤ 1092 :=
  smallPrimeAdvanceUpper 8703 64 1083 9 0x414100040c11f0400103045c100040c10b0414103041c100040c10504001030400107040c10004341030400105040c1130400103041410b
    smallCountTo8703 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8831 : oddPrimeCount 8831 ≤ 1099 :=
  smallPrimeAdvanceUpper 8767 64 1092 7 0x40c107047c103050c100040c1000414103042c13b040c105044c1030434100040c100045c103041c105040c10004001030414107040c100
    smallCountTo8767 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8885 : oddPrimeCount 8885 ≤ 1105 :=
  smallPrimeAdvanceUpper 8831 54 1099 6 0x10b040c10004001030494105040c10004d41030414111040c10004001030400107040c11304141030434153040c105
    smallCountTo8831 (by decide +kernel)

theorem base_8885 : oddPrimeCount 8885 ≤ 1105 := smallCountTo8885

set_option maxRecDepth 10000 in
private theorem smallCountTo8949 : oddPrimeCount 8949 ≤ 1111 :=
  smallPrimeAdvanceUpper 8885 64 1105 6 0x4001030444100040c107042c1030474105040c13b041c1030414125040c10b0400103053c100040c1000414103041c100040c105045c103
    smallCountTo8885 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9013 : oddPrimeCount 9013 ≤ 1120 :=
  smallPrimeAdvanceUpper 8949 64 1111 9 0x400107040c10d04441030400105040c1000400103041412f040c1070434103042c159040c11104141030400100040c10504001030400100
    smallCountTo8949 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9077 : oddPrimeCount 9077 ≤ 1126 :=
  smallPrimeAdvanceUpper 9013 64 1120 6 0x40c1470474103041c105040c100042c1030414107040c1000400103054c100040c10b0414103040010d040c105040010304bc12b040c11d
    smallCountTo9013 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9141 : oddPrimeCount 9141 ≤ 1132 :=
  smallPrimeAdvanceUpper 9077 64 1126 6 0x41c103047c105040c13d0400103041410b040c1130400103041c100040c10d0414103042c107040c1050400103045c100040c1000434103
    smallCountTo9077 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9205 : oddPrimeCount 9205 ≤ 1140 :=
  smallPrimeAdvanceUpper 9141 64 1132 8 0x4a4105040c10704001030414100040c100041c1030564135040c1000414103050c100040c1050400103041c11d040c11104001030400105
    smallCountTo9141 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9269 : oddPrimeCount 9269 ≤ 1146 :=
  smallPrimeAdvanceUpper 9205 64 1140 6 0x40c10004f4103041410d040c100045c103040010b040c10704141030400100040c105041c103042c113040c10004bc10304ec105040c10d
    smallCountTo9205 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9333 : oddPrimeCount 9333 ≤ 1153 :=
  smallPrimeAdvanceUpper 9269 64 1146 7 0x5241030414100040c10004001030494107040c10004141030444147040c10504a41030400143040c10704001030400105040c113041c103
    smallCountTo9269 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9397 : oddPrimeCount 9397 ≤ 1161 :=
  smallPrimeAdvanceUpper 9333 64 1153 8 0x414100040c10004001030434100040c12f0414103041c10b040c10504441030400107040c100054c103042c105040c12904001030414100
    smallCountTo9333 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9461 : oddPrimeCount 9461 ≤ 1170 :=
  smallPrimeAdvanceUpper 9397 64 1161 9 0x40c1070400103045c161040c10004141030400100040c105042c1030400100040c1000400103041c105040c10b04341030414107040c100
    smallCountTo9397 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9525 : oddPrimeCount 9525 ≤ 1178 :=
  smallPrimeAdvanceUpper 9461 64 1170 8 0x4001030400111040c10004141030400113040c10504d4103040010b040c100041c1030434105040c1250400103041411f040c1000564103
    smallCountTo9461 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9589 : oddPrimeCount 9589 ≤ 1183 :=
  smallPrimeAdvanceUpper 9525 64 1178 5 0x41c10d040c10004141030400107040c10504001030400129040c113042c1030524105040c1070444103041413d040c10b041c103040012b
    smallCountTo9525 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9653 : oddPrimeCount 9653 ≤ 1191 :=
  smallPrimeAdvanceUpper 9589 64 1183 8 0x40c13504141030474100040c1050434103041c100040c13b04001030400105040c10004001030414117040c11f0400103042c100040c107
    smallCountTo9589 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9717 : oddPrimeCount 9717 ≤ 1196 :=
  smallPrimeAdvanceUpper 9653 64 1191 5 0x4141030434100040c105041c103044c111040c1000400103045c105040c100042c1030414100040c159047c1030444107040c10b0414103
    smallCountTo9653 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9737 : oddPrimeCount 9737 ≤ 1199 :=
  smallPrimeAdvanceUpper 9717 20 1196 3 0x400100040c105051c1030494100040c107
    smallCountTo9717 (by decide +kernel)

theorem base_9737 : oddPrimeCount 9737 ≤ 1199 := smallCountTo9737

set_option maxRecDepth 10000 in
private theorem smallCountTo9801 : oddPrimeCount 9801 ≤ 1207 :=
  smallPrimeAdvanceUpper 9737 64 1199 8 0x4001030400105040c100041c103041410b040c12b04341030400100040c11d0414103041c100040c10504001030400107040c16104a4103
    smallCountTo9737 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9865 : oddPrimeCount 9865 ≤ 1216 :=
  smallPrimeAdvanceUpper 9801 64 1207 9 0x400105040c11104001030414100040c107042c103047c100040c1000414103040010d040c10504ac103040013b040c1000400103041c105
    smallCountTo9801 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9929 : oddPrimeCount 9929 ≤ 1223 :=
  smallPrimeAdvanceUpper 9865 64 1216 7 0x40c14704001030414107040c1290400103040010b040c10d0414103044c100040c1050400103042c117040c12f041c1030400105040c100
    smallCountTo9865 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9993 : oddPrimeCount 9993 ≤ 1228 :=
  smallPrimeAdvanceUpper 9929 64 1223 5 0x4001030414113040c10004f4103041c100040c1250414103045c107040c10504001030434100040c10b0444103050c105040c1070584103
    smallCountTo9929 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10057 : oddPrimeCount 10057 ≤ 1232 :=
  smallPrimeAdvanceUpper 9993 64 1228 4 0x41410d040c149041c1030400100040c111041410304ac10b040c1050494103041c14f040c1000400103042c105040c10d044c1030414159
    smallCountTo9993 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10121 : oddPrimeCount 10121 ≤ 1241 :=
  smallPrimeAdvanceUpper 10057 64 1232 9 0x40c10004741030400100040c10704141030400111040c105041c1030400100040c11704001030400105040c10b04001030414143040c11d
    smallCountTo10057 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10185 : oddPrimeCount 10185 ≤ 1250 :=
  smallPrimeAdvanceUpper 10121 64 1241 9 0x4d41030434107040c10004141030400100040c1050524103040010b040c10704001030400105040c100041c1030414100040c1000444103
    smallCountTo10121 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10249 : oddPrimeCount 10249 ≤ 1255 :=
  smallPrimeAdvanceUpper 10185 64 1250 5 0x4f4117040c1000414103041c165040c10504ec1030400107040c111042c1030400105040c1350434103041411d040c10704001030400125
    smallCountTo10185 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10313 : oddPrimeCount 10313 ≤ 1264 :=
  smallPrimeAdvanceUpper 10249 64 1255 9 0x40c1000414103040011f040c10504001030400100040c12b044c103041c105040c10004a41030414107040c1000400103042c10d040c100
    smallCountTo10249 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10377 : oddPrimeCount 10377 ≤ 1271 :=
  smallPrimeAdvanceUpper 10313 64 1264 7 0x4141030444100040c105045c1030400100040c100041c1030400105040c14f042c1030414100040c10d04ac103041c100040c10b0414103
    smallCountTo10313 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10441 : oddPrimeCount 10441 ≤ 1276 :=
  smallPrimeAdvanceUpper 10377 64 1271 5 0x584107040c10504341030400113040c12504001030594105040c1070474103041410b040c111041c1030400100040c1000414103042c135
    smallCountTo10377 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10505 : oddPrimeCount 10505 ≤ 1284 :=
  smallPrimeAdvanceUpper 10441 64 1276 8 0x40c105047c103041c100040c10004001030400105040c11304941030414100040c12f042c1030400111040c10704141030400100040c105
    smallCountTo10441 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10569 : oddPrimeCount 10569 ≤ 1289 :=
  smallPrimeAdvanceUpper 10505 64 1284 5 0x41c103045c100040c10d050c1030444105040c10004001030414129040c153043410304d4107040c13d0414103040013b040c1050400103
    smallCountTo10505 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10633 : oddPrimeCount 10633 ≤ 1296 :=
  smallPrimeAdvanceUpper 10569 64 1289 7 0x42c161040c107051c103044c105040c100041c1030414100040c100045c1030400167040c1000414103041c10d040c10504001030400107
    smallCountTo10569 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10697 : oddPrimeCount 10697 ≤ 1303 :=
  smallPrimeAdvanceUpper 10633 64 1296 7 0x40c10b04001030474105040c11704001030414100040c1070400103040012f040c10d041410304ec10b040c10504001030400111040c113
    smallCountTo10633 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10761 : oddPrimeCount 10761 ≤ 1310 :=
  smallPrimeAdvanceUpper 10697 64 1303 7 0x434103041c105040c10004001030414107040c14704001030444100040c10004141030400117040c105042c1030434100040c11f041c103
    smallCountTo10697 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10825 : oddPrimeCount 10825 ≤ 1314 :=
  smallPrimeAdvanceUpper 10761 64 1310 4 0x4bc105040c10b0400103041410d040c10004a4103041c100040c12b04141030400107040c1050594103044c10b040c11d047c103053c105
    smallCountTo10761 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10829 : oddPrimeCount 10829 ≤ 1314 :=
  smallPrimeAdvanceUpper 10825 4 1314 0 0x40c107
    smallCountTo10825 (by decide +kernel)

theorem base_10829 : oddPrimeCount 10829 ≤ 1314 := smallCountTo10829

set_option maxRecDepth 10000 in
private theorem smallCountTo10893 : oddPrimeCount 10893 ≤ 1324 :=
  smallPrimeAdvanceUpper 10829 64 1314 10 0x4001030414100040c125041c1030400113040c10004141030400100040c1050400103041c153040c149042c1030400105040c1000400103
    smallCountTo10829 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo10957 : oddPrimeCount 10957 ≤ 1330 :=
  smallPrimeAdvanceUpper 10893 64 1324 6 0x414111040c10b04001030434100040c107041410304f4143040c105041c103044410d040c1000400103047c105040c10004bc1030414100
    smallCountTo10893 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11021 : oddPrimeCount 11021 ≤ 1335 :=
  smallPrimeAdvanceUpper 10957 64 1330 5 0x40c161044c103042c107040c1000414103040014f040c10504001030474100040c10704441030400105040c165041c1030414117040c167
    smallCountTo10957 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11085 : oddPrimeCount 11085 ≤ 1342 :=
  smallPrimeAdvanceUpper 11021 64 1335 7 0x5241030400129040c10b0414103041c13d040c105040010304ac107040c10004001030434105040c1000400103041410b040c1070400103
    smallCountTo11021 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11149 : oddPrimeCount 11149 ≤ 1349 :=
  smallPrimeAdvanceUpper 11085 64 1342 7 0x40010d040c1000414103042c111040c105047410304a4100040c1000400103041c105040c11f04001030414107040c10d042c103051c100
    smallCountTo11085 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11213 : oddPrimeCount 11213 ≤ 1356 :=
  smallPrimeAdvanceUpper 11149 64 1349 7 0x40c11304141030400100040c10504341030400100040c100041c10304d4105040c143044c1030414100040c1170444103041c10b040c100
    smallCountTo11149 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11277 : oddPrimeCount 11277 ≤ 1362 :=
  smallPrimeAdvanceUpper 11213 64 1356 6 0x4141030434107040c105059c103042c12f040c11104001030400105040c10704001030414100040c100041c103044c13b040c1000414103
    smallCountTo11213 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11341 : oddPrimeCount 11341 ≤ 1369 :=
  smallPrimeAdvanceUpper 11277 64 1362 7 0x40011d040c1050400103041c117040c10b04001030564105040c12b04001030414100040c100043410304bc100040c1070414103044410b
    smallCountTo11277 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11405 : oddPrimeCount 11405 ≤ 1375 :=
  smallPrimeAdvanceUpper 11341 64 1369 6 0x40c105041c1030400100040c1290494103042c105040c100054c103041411f040c113040010304ec107040c1000414103040010d040c105
    smallCountTo11341 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11469 : oddPrimeCount 11469 ≤ 1381 :=
  smallPrimeAdvanceUpper 11405 64 1375 6 0x42c1030400165040c107044c1030400105040c10b041c1030414100040c1110400103040016b040c10d0414103041c149040c1050400103
    smallCountTo11405 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11533 : oddPrimeCount 11533 ≤ 1389 :=
  smallPrimeAdvanceUpper 11469 64 1381 8 0x400107040c11704341030400105040c10004001030414100040c10704001030494111040c11d04141030400129040c10504001030434113
    smallCountTo11469 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11597 : oddPrimeCount 11597 ≤ 1395 :=
  smallPrimeAdvanceUpper 11533 64 1389 6 0x40c153042c103041c105040c10004001030414107040c10b047c10304ac117040c14704141030400125040c1050400103050c100040c100
    smallCountTo11533 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11661 : oddPrimeCount 11661 ≤ 1399 :=
  smallPrimeAdvanceUpper 11597 64 1395 4 0x41c10304a4105040c10d04441030414100040c10004ec103041c11d040c1000414103059c107040c105044c10304f412b040c1000564103
    smallCountTo11597 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11725 : oddPrimeCount 11725 ≤ 1406 :=
  smallPrimeAdvanceUpper 11661 64 1399 7 0x5ac105040c107042c1030414100040c100041c1030434100040c10b04141030400100040c105045c103041c10d040c1000400103044c105
    smallCountTo11661 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11789 : oddPrimeCount 11789 ≤ 1412 :=
  smallPrimeAdvanceUpper 11725 64 1406 6 0x40c1250400103041410b040c13b0400103044411f040c1070414103042c113040c105041c103053c13d040c10004001030400105040c100
    smallCountTo11725 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11853 : oddPrimeCount 11853 ≤ 1420 :=
  smallPrimeAdvanceUpper 11789 64 1412 8 0x434103041412f040c100042c1030400107040c100041410304d4100040c10504001030400100040c10704001030434105040c111041c103
    smallCountTo11789 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11917 : oddPrimeCount 11917 ≤ 1426 :=
  smallPrimeAdvanceUpper 11853 64 1420 6 0x414147040c11d0400103040010b040c11f0414103041c16d040c1050400103042c107040c10005241030400105040c10004ac1030414111
    smallCountTo11853 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo11981 : oddPrimeCount 11981 ≤ 1436 :=
  smallPrimeAdvanceUpper 11917 64 1426 10 0x40c1070400103040014f040c10004141030400100040c10504341030444100040c10b0400103041c105040c10004001030414107040c100
    smallCountTo11917 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12045 : oddPrimeCount 12045 ≤ 1442 :=
  smallPrimeAdvanceUpper 11981 64 1436 6 0x45c1030400113040c1430414103043410b040c10504001030400129040c13d041c103042c105040c11704d41030414100040c1000400103
    smallCountTo11981 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12109 : oddPrimeCount 12109 ≤ 1449 :=
  smallPrimeAdvanceUpper 12045 64 1442 7 0x41c100040c1110414103047c107040c105042c1030400100040c10d04bc10304ac105040c10705ac1030414100040c100041c1030400100
    smallCountTo12045 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12173 : oddPrimeCount 12173 ≤ 1456 :=
  smallPrimeAdvanceUpper 12109 64 1449 7 0x40c10004141030400111040c105050c103041c10b040c13504f41030400105040c10004741030414100040c1000400103045c12b040c107
    smallCountTo12109 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12237 : oddPrimeCount 12237 ≤ 1460 :=
  smallPrimeAdvanceUpper 12173 64 1456 4 0x414103044c10d040c105041c1030524159040c100042c1030400105040c11d04001030414113040c10b04441030400107040c10d0414103
    smallCountTo12173 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12249 : oddPrimeCount 12249 ≤ 1462 :=
  smallPrimeAdvanceUpper 12237 12 1460 2 0x400100040c1050494103
    smallCountTo12237 (by decide +kernel)

theorem base_12249 : oddPrimeCount 12249 ≤ 1462 := smallCountTo12249

set_option maxRecDepth 10000 in
private theorem smallCountTo12313 : oddPrimeCount 12313 ≤ 1470 :=
  smallPrimeAdvanceUpper 12249 64 1462 8 0x400100040c10704341030400105040c100041c1030414100040c100051c103042c100040c1130414103041c100040c105047c1030434107
    smallCountTo12249 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12377 : oddPrimeCount 12377 ≤ 1476 :=
  smallPrimeAdvanceUpper 12313 64 1470 6 0x40c16d05841030400105040c100042c103041410d040c10704001030400135040c10b0414103044412f040c105054c1030564100040c100
    smallCountTo12313 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12441 : oddPrimeCount 12441 ≤ 1484 :=
  smallPrimeAdvanceUpper 12377 64 1476 8 0x400103041c105040c10d04001030414107040c100053c103044c100040c1000414103042c100040c1050444103047c100040c100041c103
    smallCountTo12377 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12505 : oddPrimeCount 12505 ≤ 1492 :=
  smallPrimeAdvanceUpper 12441 64 1484 8 0x45c105040c13b04001030414100040c111042c103041c125040c10004141030400107040c1050400103040010d040c10004741030400105
    smallCountTo12441 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12569 : oddPrimeCount 12569 ≤ 1500 :=
  smallPrimeAdvanceUpper 12505 64 1492 8 0x40c10704001030414100040c113041c103040010b040c15304141030400100040c1050400103041c100040c11d044c1030444105040c100
    smallCountTo12505 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12633 : oddPrimeCount 12633 ≤ 1507 :=
  smallPrimeAdvanceUpper 12569 64 1500 7 0x4341030414100040c117040010304a4100040c107041410304ac100040c105041c1030400100040c10b04001030434105040c1490444103
    smallCountTo12569 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12697 : oddPrimeCount 12697 ≤ 1515 :=
  smallPrimeAdvanceUpper 12633 64 1507 8 0x414100040c10004bc1030400107040c1000414103040010b040c10504d41030400113040c107047c103042c105040c100041c1030414100
    smallCountTo12633 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12761 : oddPrimeCount 12761 ≤ 1521 :=
  smallPrimeAdvanceUpper 12697 64 1515 6 0x40c10d04001030584147040c1000414103041c100040c105042c1030474107040c12f04001030400105040c10b04a41030414100040c107
    smallCountTo12697 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12825 : oddPrimeCount 12825 ≤ 1528 :=
  smallPrimeAdvanceUpper 12761 64 1521 7 0x4001030444171040c13504141030434100040c105044c103040010b040c1430400103041c105040c100045c1030414107040c1000400103
    smallCountTo12761 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12889 : oddPrimeCount 12889 ≤ 1532 :=
  smallPrimeAdvanceUpper 12825 64 1528 4 0x594100040c12904141030494100040c1050474103051c100040c10d041c103044c105040c11104f4103041414f040c10b0434103041c100
    smallCountTo12825 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo12953 : oddPrimeCount 12953 ≤ 1541 :=
  smallPrimeAdvanceUpper 12889 64 1532 9 0x40c10004141030400107040c10504001030400125040c10004001030400105040c107050c1030414111040c100041c103042c117040c100
    smallCountTo12889 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13017 : oddPrimeCount 13017 ≤ 1550 :=
  smallPrimeAdvanceUpper 12953 64 1541 9 0x414103040010d040c1050400103041c100040c11304001030400105040c11f042c1030414129040c10004001030400100040c1070414103
    smallCountTo12953 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13081 : oddPrimeCount 13081 ≤ 1555 :=
  smallPrimeAdvanceUpper 13017 64 1550 5 0x4bc11d040c105041c103054c100040c10004341030400105040c100047c103041410b040c12504001030524107040c1110414103042c167
    smallCountTo13017 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13145 : oddPrimeCount 13145 ≤ 1561 :=
  smallPrimeAdvanceUpper 13081 64 1555 6 0x40c105045c1030434100040c10704001030400105040c100041c103041410d040c100042c1030400113040c1170414103041c111040c105
    smallCountTo13081 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13209 : oddPrimeCount 13209 ≤ 1569 :=
  smallPrimeAdvanceUpper 13145 64 1561 8 0x4001030400107040c13b04001030400105040c10d04001030414100040c1070400103040010b040c14f0414103050c12b040c10504bc103
    smallCountTo13145 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13273 : oddPrimeCount 13273 ≤ 1576 :=
  smallPrimeAdvanceUpper 13209 64 1569 7 0x42c149040c1000400103041c105040c10005941030414107040c10004441030434100040c11d04141030400159040c1050400103045c10d
    smallCountTo13209 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13337 : oddPrimeCount 13337 ≤ 1583 :=
  smallPrimeAdvanceUpper 13273 64 1576 7 0x40c10b041c1030494105040c16104001030414100040c12f04d4103041c100040c1000414103044c107040c10504001030400143040c100
    smallCountTo13273 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13401 : oddPrimeCount 13401 ≤ 1588 :=
  smallPrimeAdvanceUpper 13337 64 1583 5 0x400103042c105040c10704341030414113040c11f041c103040011d040c12b04141030444100040c105042c103041c13b040c1000400103
    smallCountTo13337 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13465 : oddPrimeCount 13465 ≤ 1595 :=
  smallPrimeAdvanceUpper 13401 64 1588 7 0x434105040c10b04001030414100040c100047c103047410d040c10704141030564100040c105041c103040010b040c10004ac1030400105
    smallCountTo13401 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13529 : oddPrimeCount 13529 ≤ 1601 :=
  smallPrimeAdvanceUpper 13465 64 1595 6 0x40c100044c1030414100040c10d05841030400107040c16704141030400117040c105043410304ec100040c107042c1030400105040c153
    smallCountTo13465 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13593 : oddPrimeCount 13593 ≤ 1606 :=
  smallPrimeAdvanceUpper 13529 64 1601 5 0x41c1030414100040c10b0474103044c111040c1000414103041c147040c105040010304a4107040c10004941030444105040c16b0400103
    smallCountTo13529 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13657 : oddPrimeCount 13657 ≤ 1612 :=
  smallPrimeAdvanceUpper 13593 64 1606 6 0x414100040c10704f4103042c11f040c10004141030400135040c105040010304ac100040c10d045c103041c105040c100042c1030414107
    smallCountTo13593 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13721 : oddPrimeCount 13721 ≤ 1622 :=
  smallPrimeAdvanceUpper 13657 64 1612 10 0x40c1130434103053c100040c10b04141030400100040c10504001030400100040c100041c103051c105040c1000400103041410b040c100
    smallCountTo13657 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13785 : oddPrimeCount 13785 ≤ 1629 :=
  smallPrimeAdvanceUpper 13721 64 1622 7 0x400103041c100040c11f0414103042c107040c10504ec1030400111040c10004001030400105040c10704bc1030414117040c100041c103
    smallCountTo13721 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13849 : oddPrimeCount 13849 ≤ 1635 :=
  smallPrimeAdvanceUpper 13785 64 1629 6 0x444100040c10d04141030400125040c1050400103041c113040c1290434103045c105040c10004001030414165040c10005b410304f410b
    smallCountTo13785 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13913 : oddPrimeCount 13913 ≤ 1644 :=
  smallPrimeAdvanceUpper 13849 64 1635 9 0x40c10704141030400153040c105041c103042c100040c10004001030400105040c1110474103041410d040c10004001030400107040c100
    smallCountTo13849 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo13977 : oddPrimeCount 13977 ≤ 1649 :=
  smallPrimeAdvanceUpper 13913 64 1644 5 0x414103047c100040c105044c1030400100040c10704d41030524105040c10d041c1030414111040c1170400103040013d040c1590414103
    smallCountTo13913 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14027 : oddPrimeCount 14027 ≤ 1653 :=
  smallPrimeAdvanceUpper 13977 50 1649 4 0x107042c1030414147040c111041c1030400100040c10b04141030400100040c10505ac103041c125040c10d
    smallCountTo13977 (by decide +kernel)

theorem base_14027 : oddPrimeCount 14027 ≤ 1653 := smallCountTo14027

set_option maxRecDepth 10000 in
private theorem smallCountTo14091 : oddPrimeCount 14091 ≤ 1661 :=
  smallPrimeAdvanceUpper 14027 64 1653 8 0x4001030400105040c165044c103041410b040c10004341030400111040c1070414103042c100040c105041c1030400100040c1000524103
    smallCountTo14027 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14155 : oddPrimeCount 14155 ≤ 1665 :=
  smallPrimeAdvanceUpper 14091 64 1661 4 0x444105040c11704ec1030414100040c167042c103044c107040c11d0414103051c10d040c105050c103053c100040c10704001030400105
    smallCountTo14091 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14219 : oddPrimeCount 14219 ≤ 1670 :=
  smallPrimeAdvanceUpper 14155 64 1665 5 0x40c100041c103041411f040c1250400103040010b040c10d0414103041c117040c1050400103042c107040c100043410304f4105040c13b
    smallCountTo14155 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14283 : oddPrimeCount 14283 ≤ 1675 :=
  smallPrimeAdvanceUpper 14219 64 1670 5 0x4001030414129040c10704ac103045c11d040c10004141030400100040c10504d41030434111040c10b044c103041c105040c16d0400103
    smallCountTo14219 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14347 : oddPrimeCount 14347 ≤ 1682 :=
  smallPrimeAdvanceUpper 14283 64 1675 7 0x414107040c11f0400103044414f040c100041410304a410b040c105059c1030400100040c100041c103042c105040c10d04001030414100
    smallCountTo14283 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14411 : oddPrimeCount 14411 ≤ 1688 :=
  smallPrimeAdvanceUpper 14347 64 1682 6 0x40c171047c103041c153040c13504141030400107040c105042c1030524113040c10004001030494105040c10704001030414100040c100
    smallCountTo14347 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14475 : oddPrimeCount 14475 ≤ 1695 :=
  smallPrimeAdvanceUpper 14411 64 1688 7 0x41c1030434100040c100041410304bc100040c1050400103041c10b040c10004001030584105040c11304001030414111040c11d04a4103
    smallCountTo14411 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14539 : oddPrimeCount 14539 ≤ 1701 :=
  smallPrimeAdvanceUpper 14475 64 1695 6 0x47c100040c1070414103040012b040c105041c1030444100040c159042c103045c105040c10004341030414149040c10b04001030400107
    smallCountTo14475 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14603 : oddPrimeCount 14603 ≤ 1709 :=
  smallPrimeAdvanceUpper 14539 64 1701 8 0x40c10004141030400100040c10504001030400100040c10704441030434105040c13d041c103041411d040c1000400103042c10d040c111
    smallCountTo14539 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14667 : oddPrimeCount 14667 ≤ 1716 :=
  smallPrimeAdvanceUpper 14603 64 1709 7 0x414103041c113040c10504bc1030400107040c10004001030400105040c100042c1030414161040c1070400103040016b040c10b0414103
    smallCountTo14603 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14731 : oddPrimeCount 14731 ≤ 1723 :=
  smallPrimeAdvanceUpper 14667 64 1716 7 0x400111040c105043410304d4100040c1130494103041c105040c10004f41030414107040c12f04001030400129040c1000414103042c100
    smallCountTo14667 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14795 : oddPrimeCount 14795 ≤ 1732 :=
  smallPrimeAdvanceUpper 14731 64 1723 9 0x40c10504001030400117040c100041c1030400105040c10004741030414100040c100042c103041c100040c1000414103045c107040c105
    smallCountTo14731 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14859 : oddPrimeCount 14859 ≤ 1739 :=
  smallPrimeAdvanceUpper 14795 64 1732 7 0x400103044c171040c10d04ec1030400105040c10704001030414100040c100041c103049410b040c1000414103047c100040c105054c103
    smallCountTo14795 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14923 : oddPrimeCount 14923 ≤ 1746 :=
  smallPrimeAdvanceUpper 14859 64 1739 7 0x41c159040c100040010305ac105040c100045c1030414100040c10004d4103040012f040c1070414103044410d040c105041c10304ac100
    smallCountTo14859 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo14987 : oddPrimeCount 14987 ≤ 1753 :=
  smallPrimeAdvanceUpper 14923 64 1746 7 0x40c10b040010305b4105040c100050c1030414100040c100044c1030400107040c10d0414103040010b040c1050444103051c100040c107
    smallCountTo14923 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15051 : oddPrimeCount 15051 ≤ 1756 :=
  smallPrimeAdvanceUpper 14987 64 1753 3 0x434103042c105040c135041c103041412b040c11104001030400117040c1530414103041c100040c105042c1030434107040c1290594103
    smallCountTo14987 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15115 : oddPrimeCount 15115 ≤ 1764 :=
  smallPrimeAdvanceUpper 15051 64 1756 8 0x400105040c10b0400103041410d040c10704001030400111040c1000414103053c100040c105047c103040010b040c1000474103041c105
    smallCountTo15051 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15179 : oddPrimeCount 15179 ≤ 1771 :=
  smallPrimeAdvanceUpper 15115 64 1764 7 0x40c10d04001030414107040c10004941030400100040c1130414103040016d040c105045c103040013b040c11d041c1030400105040c12b
    smallCountTo15115 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15243 : oddPrimeCount 15243 ≤ 1778 :=
  smallPrimeAdvanceUpper 15179 64 1771 7 0x4441030414100040c10b0400103041c100040c1170414103050c107040c1050400103047c10d040c10005841030400105040c1070400103
    smallCountTo15179 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15307 : oddPrimeCount 15307 ≤ 1787 :=
  smallPrimeAdvanceUpper 15243 64 1778 9 0x41414f040c165041c103042c100040c10004141030400100040c1050400103041c111040c100040010304a4105040c100042c1030414100
    smallCountTo15243 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15371 : oddPrimeCount 15371 ≤ 1794 :=
  smallPrimeAdvanceUpper 15307 64 1787 7 0x40c13d04001030444100040c10704141030400100040c105041c103045c143040c16704001030434105040c1000400103041410b040c113
    smallCountTo15307 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15435 : oddPrimeCount 15435 ≤ 1801 :=
  smallPrimeAdvanceUpper 15371 64 1794 7 0x4001030400107040c1000414103042c100040c10505641030400149040c107044c1030400105040c111041c1030414100040c10d042c103
    smallCountTo15371 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15499 : oddPrimeCount 15499 ≤ 1809 :=
  smallPrimeAdvanceUpper 15435 64 1801 8 0x4ac100040c1000414103041c100040c10504341030400107040c100047c1030400105040c11705c41030414111040c1070400103040010b
    smallCountTo15435 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15563 : oddPrimeCount 15563 ≤ 1814 :=
  smallPrimeAdvanceUpper 15499 64 1809 5 0x40c12504141030434100040c10504ec103042c113040c10004d4103041c105040c12904001030414107040c100059c10304bc100040c14f
    smallCountTo15499 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15627 : oddPrimeCount 15627 ≤ 1820 :=
  smallPrimeAdvanceUpper 15563 64 1814 6 0x4141030400117040c10504941030400100040c10b041c103047c105040c11304001030414100040c1430434103041c100040c1110414103
    smallCountTo15563 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15691 : oddPrimeCount 15691 ≤ 1830 :=
  smallPrimeAdvanceUpper 15627 64 1820 10 0x400107040c105044c1030400100040c1000400103042c105040c10704001030414100040c100041c10304f4100040c1000414103047410d
    smallCountTo15627 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15755 : oddPrimeCount 15755 ≤ 1836 :=
  smallPrimeAdvanceUpper 15691 64 1830 6 0x40c105042c103041c129040c171045c103044c105040c10b053c1030414100040c10004001030400100040c10704141030400113040c105
    smallCountTo15691 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15819 : oddPrimeCount 15819 ≤ 1845 :=
  smallPrimeAdvanceUpper 15755 64 1836 9 0x41c103040010b040c10004341030400105040c11f04ac1030414100040c10004441030400107040c10004141030400161040c1050400103
    smallCountTo15755 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15883 : oddPrimeCount 15883 ≤ 1849 :=
  smallPrimeAdvanceUpper 15819 64 1845 4 0x434100040c107042c103051c105040c12f041c103041410d040c10b054c1030594100040c11d0414103041c13b040c10504001030400107
    smallCountTo15819 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo15947 : oddPrimeCount 15947 ≤ 1857 :=
  smallPrimeAdvanceUpper 15883 64 1849 8 0x40c1000400103045c105040c10d04001030414100040c1070400103042c100040c10004141030444159040c1050400103044c16b040c125
    smallCountTo15883 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16011 : oddPrimeCount 16011 ≤ 1863 :=
  smallPrimeAdvanceUpper 15947 64 1857 6 0x4a4103041c105040c100042c1030414107040c10004001030434113040c10b041410304ec100040c1050444103040010d040c100041c103
    smallCountTo15947 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16075 : oddPrimeCount 16075 ≤ 1870 :=
  smallPrimeAdvanceUpper 16011 64 1863 7 0x50c105040c1530494103041410b040c1110400103041c12b040c13d0414103042c107040c10504001030400100040c10004001030400105
    smallCountTo16011 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16139 : oddPrimeCount 16139 ≤ 1877 :=
  smallPrimeAdvanceUpper 16075 64 1870 7 0x40c10704341030414100040c100041c1030400111040c10004141030564100040c105051c103041c117040c10005fc1030434105040c100
    smallCountTo16075 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16203 : oddPrimeCount 16203 ≤ 1882 :=
  smallPrimeAdvanceUpper 16139 64 1877 5 0x4001030414143040c11f047410305ac10b040c1070414103044c167040c105041c103042c100040c10004001030400105040c1610444103
    smallCountTo16139 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16267 : oddPrimeCount 16267 ≤ 1889 :=
  smallPrimeAdvanceUpper 16203 64 1882 7 0x414113040c10d047c1030400107040c10004141030400100040c105043410305b4125040c10704001030400105040c147041c1030414100
    smallCountTo16203 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16331 : oddPrimeCount 16331 ≤ 1892 :=
  smallPrimeAdvanceUpper 16267 64 1889 3 0x40c135040010304a4149040c1130414103041c10b040c10504ac1030400107040c11704bc103042c105040c100044c103041411d040c107
    smallCountTo16267 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo16337 : oddPrimeCount 16337 ≤ 1893 :=
  smallPrimeAdvanceUpper 16331 6 1892 1 0x100040c111
    smallCountTo16331 (by decide +kernel)

theorem base_16337 : oddPrimeCount 16337 ≤ 1893 := smallCountTo16337

set_option maxRecDepth 10000 in
private theorem smallCountTo16383 : oddPrimeCount 16383 ≤ 1899 :=
  smallPrimeAdvanceUpper 16337 46 1893 6 0x100040c13b04141030400153040c105042c1030400100040c10d0400103041c105040c10b0400103
    smallCountTo16337 (by decide +kernel)

theorem base_16383 : oddPrimeCount 16383 ≤ 1899 := smallCountTo16383

end A085264.PrimeSeeds

/- Ten-band A085264 transfer. Codex for @dwilfand-sys, based on the earlier A085265/A085267 dyadic estimate, with prime counts independently checked at all 998401 J. Concatenate after the dyadic estimate and the A085264 seed fragment. -/

namespace A085264.SameJ

open Finset A085265.DyadicPrimeCount A085264.PrimeSeeds

def bands : List (ℕ × ℕ × ℚ × ℚ) := [
  (1600,2047,(2950/10000:ℚ),(199283/1000000:ℚ)),
  (2048,4095,(2780/10000:ℚ),(200323/1000000:ℚ)),
  (4096,8191,(2700/10000:ℚ),(205000/1000000:ℚ)),
  (8192,16383,(2889/10000:ℚ),(205000/1000000:ℚ)),
  (16384,32767,(2874/10000:ℚ),(205000/1000000:ℚ)),
  (32768,65535,(2771/10000:ℚ),(205000/1000000:ℚ)),
  (65536,131071,(2636/10000:ℚ),(205000/1000000:ℚ)),
  (131072,262143,(2495/10000:ℚ),(205000/1000000:ℚ)),
  (262144,524287,(2359/10000:ℚ),(205000/1000000:ℚ)),
  (524288,1000000,(2233/10000:ℚ),(205000/1000000:ℚ))]

private theorem count_mono {u v : ℕ} (h : u ≤ v) : oddPrimeCount u ≤ oddPrimeCount v := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hr, hprime⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hr).trans_le
    (Nat.succ_le_succ h)), hprime⟩

private theorem from_seed {J lo x cnt num den : ℕ} (hj : lo ≤ J) (hx : 2*J+1 ≤ x)
    (hcount : oddPrimeCount x ≤ cnt) (hgrid : cnt*den ≤ num*lo) (hd : 0 < den) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ ((num:ℚ)/den)*(J:ℚ) := by
  have h := (Nat.mul_le_mul_right den ((count_mono hx).trans hcount)).trans
    (hgrid.trans (Nat.mul_le_mul_left num hj))
  rw [div_mul_eq_mul_div, le_div_iff₀ (show (0:ℚ)<den by exact_mod_cast hd)]
  exact_mod_cast h

private theorem odd_half (J : ℕ) :
    oddPrimeCount (J+1) ≤ oddPrimeCount (2*(J/2)+1) := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hr,h2,hpr⟩ := Finset.mem_filter.mp hp
  have hle := Finset.mem_range.mp hr
  obtain ⟨k,hk⟩ := hpr.odd_of_ne_two (by omega)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),h2,hpr⟩

private theorem dyadic_step (J e : ℕ) (he : 0 < e) (hp : 2^e ≤ J+2) :
    oddPrimeCount (2*J+1) ≤ oddPrimeCount (2*(J/2)+1) + (2*J+1)/e := by
  have est := A085265.DyadicPrimeCount.interval (J+1) (2*J+1) e (by omega) (by omega) he hp
  exact est.trans (Nat.add_le_add_right (odd_half J) _)

private theorem band_1600 (J : ℕ) (hlo : 1600 ≤ J) (hhi : J ≤ 2047) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2950/10000:ℚ)*(J:ℚ) := by
  by_cases hu_1679 : J ≤ 1679
  · exact from_seed (lo:=1600) (x:=3359) (cnt:=472) (num:=2950) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_3359 (by decide) (by decide)
  by_cases hu_1772 : J ≤ 1772
  · exact from_seed (lo:=1680) (x:=3545) (cnt:=495) (num:=2950) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_3545 (by decide) (by decide)
  by_cases hu_1883 : J ≤ 1883
  · exact from_seed (lo:=1773) (x:=3767) (cnt:=523) (num:=2950) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_3767 (by decide) (by decide)
  by_cases hu_2012 : J ≤ 2012
  · exact from_seed (lo:=1884) (x:=4025) (cnt:=555) (num:=2950) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4025 (by decide) (by decide)
  exact from_seed (lo:=2013) (x:=4095) (cnt:=563) (num:=2950) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4095 (by decide) (by decide)

private theorem band_2048 (J : ℕ) (hlo : 2048 ≤ J) (hhi : J ≤ 4095) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2780/10000:ℚ)*(J:ℚ) := by
  by_cases hu_2075 : J ≤ 2075
  · exact from_seed (lo:=2048) (x:=4151) (cnt:=569) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4151 (by decide) (by decide)
  by_cases hu_2113 : J ≤ 2113
  · exact from_seed (lo:=2076) (x:=4227) (cnt:=577) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4227 (by decide) (by decide)
  by_cases hu_2143 : J ≤ 2143
  · exact from_seed (lo:=2114) (x:=4287) (cnt:=587) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4287 (by decide) (by decide)
  by_cases hu_2194 : J ≤ 2194
  · exact from_seed (lo:=2144) (x:=4389) (cnt:=596) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4389 (by decide) (by decide)
  by_cases hu_2255 : J ≤ 2255
  · exact from_seed (lo:=2195) (x:=4511) (cnt:=610) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4511 (by decide) (by decide)
  by_cases hu_2324 : J ≤ 2324
  · exact from_seed (lo:=2256) (x:=4649) (cnt:=627) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4649 (by decide) (by decide)
  by_cases hu_2405 : J ≤ 2405
  · exact from_seed (lo:=2325) (x:=4811) (cnt:=646) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_4811 (by decide) (by decide)
  by_cases hu_2500 : J ≤ 2500
  · exact from_seed (lo:=2406) (x:=5001) (cnt:=668) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_5001 (by decide) (by decide)
  by_cases hu_2617 : J ≤ 2617
  · exact from_seed (lo:=2501) (x:=5235) (cnt:=695) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_5235 (by decide) (by decide)
  by_cases hu_2758 : J ≤ 2758
  · exact from_seed (lo:=2618) (x:=5517) (cnt:=727) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_5517 (by decide) (by decide)
  by_cases hu_2924 : J ≤ 2924
  · exact from_seed (lo:=2759) (x:=5849) (cnt:=767) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_5849 (by decide) (by decide)
  by_cases hu_3133 : J ≤ 3133
  · exact from_seed (lo:=2925) (x:=6267) (cnt:=813) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_6267 (by decide) (by decide)
  by_cases hu_3389 : J ≤ 3389
  · exact from_seed (lo:=3134) (x:=6779) (cnt:=871) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_6779 (by decide) (by decide)
  by_cases hu_3727 : J ≤ 3727
  · exact from_seed (lo:=3390) (x:=7455) (cnt:=942) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_7455 (by decide) (by decide)
  exact from_seed (lo:=3728) (x:=8191) (cnt:=1027) (num:=2780) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_8191 (by decide) (by decide)

private theorem band_4096 (J : ℕ) (hlo : 4096 ≤ J) (hhi : J ≤ 8191) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2700/10000:ℚ)*(J:ℚ) := by
  by_cases hu_4442 : J ≤ 4442
  · exact from_seed (lo:=4096) (x:=8885) (cnt:=1105) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_8885 (by decide) (by decide)
  by_cases hu_4868 : J ≤ 4868
  · exact from_seed (lo:=4443) (x:=9737) (cnt:=1199) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_9737 (by decide) (by decide)
  by_cases hu_5414 : J ≤ 5414
  · exact from_seed (lo:=4869) (x:=10829) (cnt:=1314) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_10829 (by decide) (by decide)
  by_cases hu_6124 : J ≤ 6124
  · exact from_seed (lo:=5415) (x:=12249) (cnt:=1462) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_12249 (by decide) (by decide)
  by_cases hu_7013 : J ≤ 7013
  · exact from_seed (lo:=6125) (x:=14027) (cnt:=1653) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_14027 (by decide) (by decide)
  by_cases hu_8168 : J ≤ 8168
  · exact from_seed (lo:=7014) (x:=16337) (cnt:=1893) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_16337 (by decide) (by decide)
  exact from_seed (lo:=8169) (x:=16383) (cnt:=1899) (num:=2700) (den:=10000) (by omega) (by omega) A085264.PrimeSeeds.base_16383 (by decide) (by decide)

private theorem band_8192 (J : ℕ) (hlo : 8192 ≤ J) (hhi : J ≤ 16383) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2889/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 13 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/13 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_4096 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/13 : ℕ) : ℚ)*13 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 13
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (8192 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_16384 (J : ℕ) (hlo : 16384 ≤ J) (hhi : J ≤ 32767) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2874/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 14 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/14 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_8192 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/14 : ℕ) : ℚ)*14 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 14
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (16384 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_32768 (J : ℕ) (hlo : 32768 ≤ J) (hhi : J ≤ 65535) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2771/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 15 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/15 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_16384 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/15 : ℕ) : ℚ)*15 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 15
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (32768 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_65536 (J : ℕ) (hlo : 65536 ≤ J) (hhi : J ≤ 131071) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2636/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 16 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/16 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_32768 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/16 : ℕ) : ℚ)*16 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 16
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (65536 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_131072 (J : ℕ) (hlo : 131072 ≤ J) (hhi : J ≤ 262143) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2495/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 17 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/17 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_65536 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/17 : ℕ) : ℚ)*17 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 17
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (131072 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_262144 (J : ℕ) (hlo : 262144 ≤ J) (hhi : J ≤ 524287) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2359/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 18 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/18 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_131072 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/18 : ℕ) : ℚ)*18 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 18
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (262144 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_524288 (J : ℕ) (hlo : 524288 ≤ J) (hhi : J ≤ 1000000) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2233/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 19 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/19 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_262144 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/19 : ℕ) : ℚ)*19 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 19
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (524288 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem all_bands : ∀ b ∈ bands, ∀ J : ℕ, b.1 ≤ J → J ≤ b.2.1 →
    (oddPrimeCount (2*J+1) : ℚ) ≤ b.2.2.1*(J:ℚ) := by
  unfold bands
  refine List.forall_mem_cons.mpr ⟨band_1600, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_2048, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_4096, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_8192, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_16384, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_32768, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_65536, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_131072, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_262144, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_524288, ?_⟩
  simp

theorem prime_count_le {lo hi J : ℕ} {alpha recip : ℚ}
    (hband : (lo,hi,alpha,recip) ∈ bands) (hlo : lo ≤ J) (hhi : J ≤ hi) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ alpha*(J:ℚ) := all_bands _ hband J hlo hhi

theorem band_exists {J : ℕ} (hlo : 1600 ≤ J) (hhi : J ≤ 1000000) :
    ∃ (lo hi : ℕ) (alpha recip : ℚ), (lo,hi,alpha,recip) ∈ bands ∧ lo ≤ J ∧ J ≤ hi := by
  by_cases until_2047 : J ≤ 2047
  · exact ⟨1600,2047,(2950/10000:ℚ),(199283/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_4095 : J ≤ 4095
  · exact ⟨2048,4095,(2780/10000:ℚ),(200323/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_8191 : J ≤ 8191
  · exact ⟨4096,8191,(2700/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_16383 : J ≤ 16383
  · exact ⟨8192,16383,(2889/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_32767 : J ≤ 32767
  · exact ⟨16384,32767,(2874/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_65535 : J ≤ 65535
  · exact ⟨32768,65535,(2771/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_131071 : J ≤ 131071
  · exact ⟨65536,131071,(2636/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_262143 : J ≤ 262143
  · exact ⟨131072,262143,(2495/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_524287 : J ≤ 524287
  · exact ⟨262144,524287,(2359/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩
  exact ⟨524288,1000000,(2233/10000:ℚ),(205000/1000000:ℚ),by decide,by omega,by omega⟩

end A085264.SameJ

namespace A085265.SameJ

open Finset

def oddPrimes (x : ℕ) : Finset ℕ := (range (x+1)).filter (fun p => 2 < p ∧ p.Prime)
def active (J : ℕ) : Finset ℕ := (oddPrimes (2*J+1)).filter (fun p => p^2 ≤ 2*J)
def recip (A : Finset ℕ) : ℚ := ∑ p ∈ A, 1/(p:ℚ)^2

private lemma recip_mono {A B : Finset ℕ} (h : A ⊆ B) : recip A ≤ recip B :=
  sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

theorem mask_active {J : ℕ} {A : Finset ℕ} (hJ : 300 ≤ J)
    (hA : A ⊆ {3,5,7,11,13,17}) : A ⊆ active J := by
  intro p hp
  have tab : ∀ q ∈ ({3,5,7,11,13,17} : Finset ℕ), 2 < q ∧ q.Prime ∧ q ≤ 17 := by decide
  obtain ⟨h2,hprime,hle⟩ := tab p (hA hp)
  have sq := Nat.pow_le_pow_left hle 2
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), h2, hprime⟩, by omega⟩

theorem cost {J : ℕ} {S A : Finset ℕ} {α R : ℚ} (haS : A ⊆ S)
    (ha : A ⊆ active J) (hc : ((oddPrimes (2*J+1)).card : ℚ) ≤ α*(J:ℚ))
    (hr : recip (active J) ≤ R) :
    ((∑ p ∈ oddPrimes (2*J+1) \ S, (2*J/(p^2)+1) : ℕ) : ℚ) ≤
      (J:ℚ)*(α+2*(R-recip A))-(A.card:ℚ) := by
  let P := oddPrimes (2*J+1)
  let E := P \ S
  let B := E.filter (fun p => p^2 ≤ 2*J)
  have out {p : ℕ} (hp : p ∈ E) : p ∉ A :=
    fun h => (mem_sdiff.mp hp).2 (haS h)
  have disj : Disjoint E A := disjoint_left.mpr fun _ hp => out hp
  have bdisj : Disjoint B A := disjoint_left.mpr fun _ hp => out (mem_filter.mp hp).1
  have esub : E ∪ A ⊆ P := union_subset sdiff_subset (fun _ h => (mem_filter.mp (ha h)).1)
  have bsub : B ∪ A ⊆ active J := by
    apply union_subset _ ha
    intro p hp
    obtain ⟨he, hs⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_sdiff.mp he).1, hs⟩
  have rsum : recip B + recip A ≤ R := by
    calc
      _ = recip (B ∪ A) := (sum_union bdisj).symm
      _ ≤ _ := (recip_mono bsub).trans hr
  have csum : (E.card:ℚ) + (A.card:ℚ) ≤ α*(J:ℚ) := by
    have cn : E.card + A.card ≤ P.card := by
      rw [← card_union_of_disjoint disj]
      exact card_le_card esub
    exact (show (E.card:ℚ) + (A.card:ℚ) ≤ (P.card:ℚ) by exact_mod_cast cn).trans hc
  have remove : (∑ p ∈ B, 2*J/(p^2)) = ∑ p ∈ E, 2*J/(p^2) := by
    apply sum_subset (filter_subset _ _)
    intro p hp hn
    exact Nat.div_eq_of_lt (lt_of_not_ge (fun hs => hn (mem_filter.mpr ⟨hp,hs⟩)))
  have hf : ((∑ p ∈ E, 2*J/(p^2) : ℕ) : ℚ) ≤ 2*(J:ℚ)*(R-recip A) := by
    rw [← remove, Nat.cast_sum]
    calc
      _ ≤ ∑ p ∈ B, 2*(J:ℚ)*(1/(p:ℚ)^2) := by
        apply sum_le_sum
        intro p hp
        have hp0 : 0 < p := by
          have hodd := (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2.1
          omega
        rw [mul_one_div]
        apply (le_div_iff₀ (show 0 < (p:ℚ)^2 by positivity)).mpr
        exact_mod_cast Nat.div_mul_le_self (2*J) (p^2)
      _ = 2*(J:ℚ)*recip B := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [rsum]) (by positivity)
  change ((∑ p ∈ E, (2*J/(p^2)+1) : ℕ) : ℚ) ≤ _
  rw [sum_add_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_add]
  calc
    _ ≤ 2*(J:ℚ)*(R-recip A) + (α*(J:ℚ)-(A.card:ℚ)) :=
      add_le_add hf (by linarith only [csum])
    _ = _ := by ring

private theorem active_recip_of_hi {J H T : ℕ} (hJ : J ≤ H) (hT : 2*H < (T+1)^2) :
    recip (active J) ≤ recip (oddPrimes T) := by
  apply recip_mono
  intro p hp
  obtain ⟨hmem,hs⟩ := mem_filter.mp hp
  have hle : p ≤ T := by
    by_contra! hh
    have bound := Nat.pow_le_pow_left (show T+1 ≤ p by omega) 2
    omega
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hmem).2⟩

theorem active_recip_420 {J : ℕ} (h : J ≤ 420) : recip (active J) ≤ 96911/500000 :=
  (active_recip_of_hi (T := 28) h (by decide)).trans (by decide +kernel)

theorem active_recip_599 {J : ℕ} (h : J ≤ 599) : recip (active J) ≤ 49013/250000 :=
  (active_recip_of_hi (T := 34) h (by decide)).trans (by decide +kernel)

theorem active_recip_1023 {J : ℕ} (h : J ≤ 1023) : recip (active J) ≤ 98959/500000 :=
  (active_recip_of_hi (T := 45) h (by decide)).trans (by decide +kernel)

theorem active_recip_2047 {J : ℕ} (h : J ≤ 2047) : recip (active J) ≤ 199283/1000000 :=
  (active_recip_of_hi (T := 63) h (by decide)).trans (by decide +kernel)

theorem active_recip_4095 {J : ℕ} (h : J ≤ 4095) : recip (active J) ≤ 200323/1000000 :=
  (active_recip_of_hi (T := 90) h (by decide)).trans (by decide +kernel)

private theorem odd_reciprocal_step {p T : ℕ} (hT : 1 ≤ T) (hTp : T < p) :
    1/(p : ℚ)^2 + 1/(2*((p : ℚ)+1)) ≤ 1/(2*(T : ℚ)) := by
  have hpos : (0 : ℚ) < T := by exact_mod_cast (show 0 < T by omega)
  have hle : (T : ℚ)+1 ≤ p := by exact_mod_cast (show T+1 ≤ p by omega)
  have hm : 0 < (p : ℚ)-1 := by linarith
  have hp : 0 < (p : ℚ)+1 := by positivity
  have htel : 1/(2*((p : ℚ)-1)) - 1/(2*((p : ℚ)+1)) =
      1/(((p : ℚ)-1)*((p : ℚ)+1)) := by
    field_simp [hm.ne', hp.ne'] <;> ring
  have hrec : 1/(p : ℚ)^2 ≤ 1/(((p : ℚ)-1)*((p : ℚ)+1)) :=
    one_div_le_one_div_of_le (mul_pos hm hp) (by nlinarith)
  have hstart : 1/(2*((p : ℚ)-1)) ≤ 1/(2*(T : ℚ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

private theorem odd_reciprocal_tail_aux (count : ℕ) (P : Finset ℕ)
    (hcard : P.card = count) (T : ℕ) (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) := by
  induction count generalizing P T with
  | zero =>
    have he := Finset.card_eq_zero.mp hcard
    subst P
    simp only [Finset.sum_empty]
    positivity
  | succ count ih =>
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    let p := P.min' hne
    have hp : p ∈ P := P.min'_mem hne
    have hcard' : (P.erase p).card = count := by
      rw [Finset.card_erase_of_mem hp, hcard] <;> omega
    have hsub {q : ℕ} (hq : q ∈ P.erase p) : q ∈ P := (Finset.mem_erase.mp hq).2
    have hnext (q : ℕ) (hq : q ∈ P.erase p) : p+1 < q := by
      have hdiff := (Finset.mem_erase.mp hq).1
      have hmin : p ≤ q := P.min'_le q (hsub hq)
      obtain ⟨hp2,hpp⟩ := hP p hp
      obtain ⟨hq2,hqp⟩ := hP q (hsub hq)
      obtain ⟨i,hi⟩ := hpp.odd_of_ne_two (by omega)
      obtain ⟨j,hj⟩ := hqp.odd_of_ne_two (by omega)
      omega
    have htail := ih (P.erase p) hcard' (p+1) (by omega)
      (fun q hq => hP q (hsub hq)) hnext
    rw [← Finset.add_sum_erase P (fun q => 1/(q : ℚ)^2) hp]
    calc
      _ ≤ 1/(p : ℚ)^2 + 1/(2*(((p+1 : ℕ) : ℚ))) := add_le_add le_rfl htail
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using
        odd_reciprocal_step hT (hcut p hp)

/-- A finite subset of the odd primes past `T` has reciprocal-square sum at
most `1/(2T)`, by telescoping along successive odd integers. -/
theorem oddPrimeReciprocalTail {P : Finset ℕ} {T : ℕ} (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) :=
  odd_reciprocal_tail_aux P.card P rfl T hT hP hcut

theorem active_recip_global (J : ℕ) : recip (active J) ≤ 41/200 := by
  let Q := active J
  let low := Q.filter (fun p => p ≤ 128)
  let high := Q.filter (fun p => ¬p ≤ 128)
  have prop (p : ℕ) (hp : p ∈ Q) : 2 < p ∧ p.Prime :=
    (mem_filter.mp (mem_filter.mp hp).1).2
  have sub : low ⊆ oddPrimes 128 := by
    intro p hp
    obtain ⟨hq,hle⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), prop p hq⟩
  have tail : recip high ≤ 1/(2*(128:ℚ)) :=
    oddPrimeReciprocalTail (by decide) (fun p hp => prop p (mem_filter.mp hp).1)
      (fun _ hp => lt_of_not_ge (mem_filter.mp hp).2)
  have partition : recip low + recip high = recip Q :=
    sum_filter_add_sum_filter_not Q (fun p => p ≤ 128) (fun p => 1/(p:ℚ)^2)
  have finite : recip (oddPrimes 128) + 1/(2*(128:ℚ)) ≤ 41/200 := by decide +kernel
  exact partition ▸ (add_le_add (recip_mono sub) tail).trans finite

end A085265.SameJ

namespace A085264.SameJ

private theorem reciprocal_bands :
    ∀ b ∈ bands, ∀ J : ℕ, J ≤ b.2.1 →
      A085265.SameJ.recip (A085265.SameJ.active J) ≤ b.2.2.2 := by
  unfold bands
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_2047 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_4095 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  simp

theorem active_recip_le {lo hi J : ℕ} {α R : ℚ}
    (hband : (lo,hi,α,R) ∈ bands) (_hlo : lo ≤ J) (hhi : J ≤ hi) :
    A085265.SameJ.recip (A085265.SameJ.active J) ≤ R :=
  reciprocal_bands _ hband J hhi

end A085264.SameJ

/- Fixed-J strict profile inequalities for the 10 bands. Each certificate checks
the first admissible J in its band and the nonnegative slope for all larger J. -/

namespace A085264.SameJ

open scoped BigOperators

private def profilePrimes : Finset ℕ := {3,5,7,11,13,17}

private def firstProfileJ (lo : ℕ) (A : Finset ℕ) (t : ℕ) : ℕ :=
  max lo (((∏ p ∈ A, p) * 19^t - 1) / 2)

private def profileError (k : ℕ) : ℚ := if k = 0 then 0 else (2:ℚ)^(k-1)

private def profileSlope (α R : ℚ) (A : Finset ℕ) (t : ℕ) : ℚ :=
  (∏ p ∈ A, (1-1/(p:ℚ))) * (18/19:ℚ)^t - (α + 2*(R-A085265.SameJ.recip A))

private def anchorProfile (row : ℕ × ℕ × ℚ × ℚ) : Prop :=
  ∀ A ∈ profilePrimes.powerset, ∀ t : Fin 5,
    firstProfileJ row.1 A t.val ≤ row.2.1 →
      0 ≤ profileSlope row.2.2.1 row.2.2.2 A t.val ∧
        100 + profileError (A.card+t.val) - (A.card:ℚ) <
          (firstProfileJ row.1 A t.val:ℚ) * profileSlope row.2.2.1 row.2.2.2 A t.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_1600 :
    anchorProfile (1600,2047,(2950/10000:ℚ),(199283/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_2048 :
    anchorProfile (2048,4095,(2780/10000:ℚ),(200323/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_4096 :
    anchorProfile (4096,8191,(2700/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_8192 :
    anchorProfile (8192,16383,(2889/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_16384 :
    anchorProfile (16384,32767,(2874/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_32768 :
    anchorProfile (32768,65535,(2771/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_65536 :
    anchorProfile (65536,131071,(2636/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_131072 :
    anchorProfile (131072,262143,(2495/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_262144 :
    anchorProfile (262144,524287,(2359/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_524288 :
    anchorProfile (524288,1000000,(2233/10000:ℚ),(205000/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

private theorem allProfileAnchors : ∀ b ∈ bands, anchorProfile b := by
  unfold bands
  refine List.forall_mem_cons.mpr ⟨profileAnchor_1600, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_2048, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_4096, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_8192, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_16384, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_32768, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_65536, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_131072, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_262144, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_524288, ?_⟩
  simp

theorem profile_all {lo hi J : ℕ} {α R : ℚ}
    (hband : (lo,hi,α,R) ∈ bands) (hlo : lo ≤ J) (hhi : J ≤ hi)
    (A : Finset ℕ) (hA : A ⊆ ({3,5,7,11,13,17} : Finset ℕ))
    (t : ℕ) (ht : t < 5) (hprod : (∏ p ∈ A, p) * 19^t ≤ 2*J+2) :
    (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) - (A.card:ℚ) +
      (100+(if A.card+t = 0 then 0 else (2:ℚ)^(A.card+t-1))) <
      (J:ℚ)*(∏ p ∈ A, (1-1/(p:ℚ)))*(18/19:ℚ)^t := by
  have hmin : firstProfileJ lo A t ≤ J := by
    unfold firstProfileJ
    exact max_le hlo (by omega)
  have hmem : A ∈ profilePrimes.powerset := Finset.mem_powerset.mpr hA
  obtain ⟨hslope, hanchor⟩ :=
    allProfileAnchors _ hband A hmem ⟨t,ht⟩ (hmin.trans hhi)
  change 0 ≤ profileSlope α R A t at hslope
  change 100 + profileError (A.card+t) - (A.card:ℚ) <
    (firstProfileJ lo A t:ℚ) * profileSlope α R A t at hanchor
  have hq : (firstProfileJ lo A t:ℚ) ≤ (J:ℚ) := by exact_mod_cast hmin
  have gap := hanchor.trans_le (mul_le_mul_of_nonneg_right hq hslope)
  change (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) - (A.card:ℚ) +
    (100+profileError (A.card+t)) < _
  calc
    _ = (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) +
        (100+profileError (A.card+t)-(A.card:ℚ)) := by ring
    _ < (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) +
        (J:ℚ)*profileSlope α R A t := by linarith only [gap]
    _ = _ := by unfold profileSlope; ring

end A085264.SameJ

namespace A085264.SameJ.Assembly

private def smallPrimes : Finset ℕ := {3, 5, 7, 11, 13, 17}

private def largeRho (A : Finset ℕ) : ℚ := ∏ p ∈ A, (1-1/(p:ℚ))

private def err (k : ℕ) : ℚ := if k = 0 then 0 else (2:ℚ)^(k-1)

private theorem rho_nonneg' {S : Finset ℕ} (h : ∀ p ∈ S, 2 < p) : 0 ≤ largeRho S := by
  apply Finset.prod_nonneg
  intro p hp
  have h₁ : (1:ℚ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := h p hp; omega)
  exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℚ) < p)).mpr h₁)

theorem combine {J : ℕ} {S : Finset ℕ} {α R : ℚ}
    (hlo : 1600 ≤ J) (hhi : J ≤ 1000000) (hS : ∀ p ∈ S, 2 < p ∧ p.Prime)
    (hB : (∏ p ∈ S, p) ≤ 2*J+2)
    (hcount : ((A085265.SameJ.oddPrimes (2*J+1)).card : ℚ) ≤ α*(J:ℚ))
    (hrecip : A085265.SameJ.recip (A085265.SameJ.active J) ≤ R)
    (hprofile : ∀ A : Finset ℕ, A ⊆ smallPrimes → ∀ t : ℕ, t < 5 →
      (∏ p ∈ A, p) * 19^t ≤ 2*J+2 →
      (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) - (A.card:ℚ) + (100+err (A.card+t)) <
        (J:ℚ)*largeRho A*(18/19:ℚ)^t) :
    ((∑ p ∈ A085265.SameJ.oddPrimes (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
      (100+err S.card) < (J:ℚ)*largeRho S := by
  let A := S ∩ smallPrimes
  let T := S \ A
  have haS : A ⊆ S := Finset.inter_subset_left
  have hat : Disjoint A T := Finset.disjoint_left.mpr
    (fun _ ha ht => (Finset.mem_sdiff.mp ht).2 ha)
  have hsplit : A ∪ T = S := Finset.union_sdiff_of_subset haS
  have card : A.card+T.card = S.card := by rw [← Finset.card_union_of_disjoint hat,hsplit]
  have large (p : ℕ) (hp : p ∈ T) : 19 ≤ p := by
    obtain ⟨hs,ha⟩ := Finset.mem_sdiff.mp hp
    have tab : ∀ t : Fin 19, 2 < t.val → Nat.Prime t.val → t.val ∈ smallPrimes := by decide
    by_contra! h
    have prop := hS p hs
    exact ha (Finset.mem_inter.mpr ⟨hs,tab ⟨p,h⟩ prop.1 prop.2⟩)
  have pT : 19^T.card ≤ ∏ p ∈ T,p := by
    simpa only [Finset.prod_const] using (Finset.prod_le_prod' (fun p hp => large p hp))
  have pA : (∏ p ∈ A,p)*19^T.card ≤ 2*J+2 := calc
    _ ≤ _ := Nat.mul_le_mul_left (∏ p ∈ A,p) pT
    _ = ∏ p ∈ S,p := by rw [← Finset.prod_union hat,hsplit]
    _ ≤ _ := hB
  have pApos : 0 < ∏ p ∈ A,p := Finset.prod_pos (fun p hp => by have := (hS p (haS hp)).1; omega)
  have pTle : 19^T.card ≤ 2*J+2 := (Nat.le_mul_of_pos_left _ pApos).trans pA
  have ht : T.card < 5 := by
    by_contra! hk
    have high := Nat.pow_le_pow_right (by decide : 0 < 19) hk
    omega
  have hTρ : (18/19:ℚ)^T.card ≤ largeRho T := by
    have point (p : ℕ) (hp : p ∈ T) : (18/19:ℚ) ≤ 1-1/(p:ℚ) := by
      have pq : (19:ℚ) ≤ p := by exact_mod_cast large p hp
      have inf := one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 19) pq
      linarith
    have bound (U : Finset ℕ) (hu : ∀ p ∈ U, (18/19:ℚ) ≤ 1-1/(p:ℚ)) :
        (18/19:ℚ)^U.card ≤ largeRho U := by
      induction U using Finset.induction_on with
      | empty => simp [largeRho]
      | @insert p U hp ih =>
        have hp' := hu p (Finset.mem_insert_self p U)
        have hi := ih (fun q hq => hu q (Finset.mem_insert_of_mem hq))
        have h := mul_le_mul hp' hi (by positivity)
          (by linarith only [hp'] : 0 ≤ 1-1/(p:ℚ))
        simpa [largeRho, hp, pow_succ, mul_comm] using h
    exact bound T point
  have hρA := rho_nonneg' (S := A) (fun p hp => (hS p (haS hp)).1)
  have hrho : largeRho A * largeRho T = largeRho S := by
    unfold largeRho
    rw [← Finset.prod_union hat,hsplit]
  have hright : (J:ℚ)*largeRho A*(18/19:ℚ)^T.card ≤ (J:ℚ)*largeRho S := calc
    _ = (J:ℚ)*(largeRho A*(18/19:ℚ)^T.card) := by ring
    _ ≤ (J:ℚ)*(largeRho A*largeRho T) := by gcongr
    _ = _ := by rw [hrho]
  have hsmall : A ⊆ smallPrimes := Finset.inter_subset_right
  have hactive : A ⊆ A085265.SameJ.active J := A085265.SameJ.mask_active (by omega) hsmall
  have lower := hprofile A hsmall T.card ht pA
  have upper := A085265.SameJ.cost haS hactive hcount hrecip
  rw [← card]
  exact ((add_le_add upper (le_refl (100+err (A.card+T.card)))).trans_lt lower).trans_le hright

end A085264.SameJ.Assembly

namespace A085264.SameJ.Assembly

theorem budget {J : ℕ} {S : Finset ℕ} (hlo : 1600 ≤ J) (hhi : J ≤ 1000000)
    (hS : ∀ p ∈ S, 2 < p ∧ p.Prime) (hB : (∏ p ∈ S, p) ≤ 2*J+2) :
    ((∑ p ∈ A085265.SameJ.oddPrimes (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
      (100+(if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
        (J:ℚ)*(∏ p ∈ S, (1-1/(p:ℚ))) := by
  obtain ⟨lo, hi, α, R, hband, hlow, hhigh⟩ := A085264.SameJ.band_exists hlo hhi
  apply combine (α := α) (R := R) hlo hhi hS hB
  · exact A085264.SameJ.prime_count_le hband hlow hhigh
  · exact A085264.SameJ.active_recip_le hband hlow hhigh
  · intro A ha t ht hprod
    exact A085264.SameJ.profile_all hband hlow hhigh A ha t ht hprod

end A085264.SameJ.Assembly

theorem OMA.solution : OMA.R_oeis_a085264_R1_H2_R1.H1 := by
  intro J S hlo hhi hS hB
  exact A085264.SameJ.Assembly.budget hlo hhi hS hB

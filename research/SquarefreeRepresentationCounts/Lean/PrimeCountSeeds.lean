/- A085264 prime-count seeds. Codex for @dwilfand-sys. Computed independently by the sieve of Eratosthenes; the Lean statements instead check all counts by disjoint integer segments. Concatenate after A085265.DyadicPrimeCount definitions. -/

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

private theorem smallPrimeAdvance (a h c d : ℕ)
    (ha : oddPrimeCount a = c) (hd : smallPrimeSegment a h = d) :
    oddPrimeCount (a+h) = c+d := by
  have split : oddPrimeCount (a+h) = oddPrimeCount a + smallPrimeSegment a h := by
    rw [smallPrimeCount_sum (a+h), smallPrimeCount_sum a,
      show a+h+1 = a+1+h by omega, Finset.sum_range_add, smallPrimeSegment_sum]
  rw [split, ha, hd]

private theorem smallCountTo0 : oddPrimeCount 0 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo48 : oddPrimeCount 48 = 14 :=
  smallPrimeAdvance 0 48 0 14 smallCountTo0 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo96 : oddPrimeCount 96 = 23 :=
  smallPrimeAdvance 48 48 14 9 smallCountTo48 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo144 : oddPrimeCount 144 = 33 :=
  smallPrimeAdvance 96 48 23 10 smallCountTo96 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo192 : oddPrimeCount 192 = 42 :=
  smallPrimeAdvance 144 48 33 9 smallCountTo144 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo240 : oddPrimeCount 240 = 51 :=
  smallPrimeAdvance 192 48 42 9 smallCountTo192 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo288 : oddPrimeCount 288 = 60 :=
  smallPrimeAdvance 240 48 51 9 smallCountTo240 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo336 : oddPrimeCount 336 = 66 :=
  smallPrimeAdvance 288 48 60 6 smallCountTo288 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo384 : oddPrimeCount 384 = 75 :=
  smallPrimeAdvance 336 48 66 9 smallCountTo336 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo432 : oddPrimeCount 432 = 82 :=
  smallPrimeAdvance 384 48 75 7 smallCountTo384 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo480 : oddPrimeCount 480 = 91 :=
  smallPrimeAdvance 432 48 82 9 smallCountTo432 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo528 : oddPrimeCount 528 = 98 :=
  smallPrimeAdvance 480 48 91 7 smallCountTo480 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo576 : oddPrimeCount 576 = 104 :=
  smallPrimeAdvance 528 48 98 6 smallCountTo528 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo624 : oddPrimeCount 624 = 113 :=
  smallPrimeAdvance 576 48 104 9 smallCountTo576 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo672 : oddPrimeCount 672 = 120 :=
  smallPrimeAdvance 624 48 113 7 smallCountTo624 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo720 : oddPrimeCount 720 = 127 :=
  smallPrimeAdvance 672 48 120 7 smallCountTo672 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo768 : oddPrimeCount 768 = 134 :=
  smallPrimeAdvance 720 48 127 7 smallCountTo720 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo816 : oddPrimeCount 816 = 140 :=
  smallPrimeAdvance 768 48 134 6 smallCountTo768 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo864 : oddPrimeCount 864 = 149 :=
  smallPrimeAdvance 816 48 140 9 smallCountTo816 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo912 : oddPrimeCount 912 = 155 :=
  smallPrimeAdvance 864 48 149 6 smallCountTo864 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo960 : oddPrimeCount 960 = 161 :=
  smallPrimeAdvance 912 48 155 6 smallCountTo912 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1008 : oddPrimeCount 1008 = 167 :=
  smallPrimeAdvance 960 48 161 6 smallCountTo960 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1056 : oddPrimeCount 1056 = 176 :=
  smallPrimeAdvance 1008 48 167 9 smallCountTo1008 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1104 : oddPrimeCount 1104 = 184 :=
  smallPrimeAdvance 1056 48 176 8 smallCountTo1056 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1152 : oddPrimeCount 1152 = 189 :=
  smallPrimeAdvance 1104 48 184 5 smallCountTo1104 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1200 : oddPrimeCount 1200 = 195 :=
  smallPrimeAdvance 1152 48 189 6 smallCountTo1152 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1248 : oddPrimeCount 1248 = 202 :=
  smallPrimeAdvance 1200 48 195 7 smallCountTo1200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1296 : oddPrimeCount 1296 = 209 :=
  smallPrimeAdvance 1248 48 202 7 smallCountTo1248 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1344 : oddPrimeCount 1344 = 216 :=
  smallPrimeAdvance 1296 48 209 7 smallCountTo1296 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1392 : oddPrimeCount 1392 = 220 :=
  smallPrimeAdvance 1344 48 216 4 smallCountTo1344 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1440 : oddPrimeCount 1440 = 227 :=
  smallPrimeAdvance 1392 48 220 7 smallCountTo1392 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1488 : oddPrimeCount 1488 = 235 :=
  smallPrimeAdvance 1440 48 227 8 smallCountTo1440 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1536 : oddPrimeCount 1536 = 241 :=
  smallPrimeAdvance 1488 48 235 6 smallCountTo1488 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1584 : oddPrimeCount 1584 = 249 :=
  smallPrimeAdvance 1536 48 241 8 smallCountTo1536 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1632 : oddPrimeCount 1632 = 257 :=
  smallPrimeAdvance 1584 48 249 8 smallCountTo1584 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1680 : oddPrimeCount 1680 = 262 :=
  smallPrimeAdvance 1632 48 257 5 smallCountTo1632 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1728 : oddPrimeCount 1728 = 268 :=
  smallPrimeAdvance 1680 48 262 6 smallCountTo1680 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1776 : oddPrimeCount 1776 = 273 :=
  smallPrimeAdvance 1728 48 268 5 smallCountTo1728 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1824 : oddPrimeCount 1824 = 280 :=
  smallPrimeAdvance 1776 48 273 7 smallCountTo1776 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1872 : oddPrimeCount 1872 = 285 :=
  smallPrimeAdvance 1824 48 280 5 smallCountTo1824 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1920 : oddPrimeCount 1920 = 292 :=
  smallPrimeAdvance 1872 48 285 7 smallCountTo1872 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo1968 : oddPrimeCount 1968 = 296 :=
  smallPrimeAdvance 1920 48 292 4 smallCountTo1920 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2016 : oddPrimeCount 2016 = 304 :=
  smallPrimeAdvance 1968 48 296 8 smallCountTo1968 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2064 : oddPrimeCount 2064 = 310 :=
  smallPrimeAdvance 2016 48 304 6 smallCountTo2016 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2112 : oddPrimeCount 2112 = 317 :=
  smallPrimeAdvance 2064 48 310 7 smallCountTo2064 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2160 : oddPrimeCount 2160 = 324 :=
  smallPrimeAdvance 2112 48 317 7 smallCountTo2112 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2208 : oddPrimeCount 2208 = 328 :=
  smallPrimeAdvance 2160 48 324 4 smallCountTo2160 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2256 : oddPrimeCount 2256 = 334 :=
  smallPrimeAdvance 2208 48 328 6 smallCountTo2208 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2304 : oddPrimeCount 2304 = 341 :=
  smallPrimeAdvance 2256 48 334 7 smallCountTo2256 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2352 : oddPrimeCount 2352 = 348 :=
  smallPrimeAdvance 2304 48 341 7 smallCountTo2304 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2400 : oddPrimeCount 2400 = 356 :=
  smallPrimeAdvance 2352 48 348 8 smallCountTo2352 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2448 : oddPrimeCount 2448 = 362 :=
  smallPrimeAdvance 2400 48 356 6 smallCountTo2400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2496 : oddPrimeCount 2496 = 366 :=
  smallPrimeAdvance 2448 48 362 4 smallCountTo2448 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2544 : oddPrimeCount 2544 = 371 :=
  smallPrimeAdvance 2496 48 366 5 smallCountTo2496 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2592 : oddPrimeCount 2592 = 376 :=
  smallPrimeAdvance 2544 48 371 5 smallCountTo2544 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2640 : oddPrimeCount 2640 = 381 :=
  smallPrimeAdvance 2592 48 376 5 smallCountTo2592 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2688 : oddPrimeCount 2688 = 389 :=
  smallPrimeAdvance 2640 48 381 8 smallCountTo2640 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2736 : oddPrimeCount 2736 = 398 :=
  smallPrimeAdvance 2688 48 389 9 smallCountTo2688 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2784 : oddPrimeCount 2784 = 403 :=
  smallPrimeAdvance 2736 48 398 5 smallCountTo2736 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2832 : oddPrimeCount 2832 = 409 :=
  smallPrimeAdvance 2784 48 403 6 smallCountTo2784 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2880 : oddPrimeCount 2880 = 416 :=
  smallPrimeAdvance 2832 48 409 7 smallCountTo2832 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2928 : oddPrimeCount 2928 = 422 :=
  smallPrimeAdvance 2880 48 416 6 smallCountTo2880 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo2976 : oddPrimeCount 2976 = 428 :=
  smallPrimeAdvance 2928 48 422 6 smallCountTo2928 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3024 : oddPrimeCount 3024 = 433 :=
  smallPrimeAdvance 2976 48 428 5 smallCountTo2976 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3072 : oddPrimeCount 3072 = 438 :=
  smallPrimeAdvance 3024 48 433 5 smallCountTo3024 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3120 : oddPrimeCount 3120 = 443 :=
  smallPrimeAdvance 3072 48 438 5 smallCountTo3072 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3168 : oddPrimeCount 3168 = 447 :=
  smallPrimeAdvance 3120 48 443 4 smallCountTo3120 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3216 : oddPrimeCount 3216 = 453 :=
  smallPrimeAdvance 3168 48 447 6 smallCountTo3168 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3264 : oddPrimeCount 3264 = 460 :=
  smallPrimeAdvance 3216 48 453 7 smallCountTo3216 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3312 : oddPrimeCount 3312 = 464 :=
  smallPrimeAdvance 3264 48 460 4 smallCountTo3264 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3359 : oddPrimeCount 3359 = 472 :=
  smallPrimeAdvance 3312 47 464 8 smallCountTo3312 (by decide +kernel)

theorem base_3359 : oddPrimeCount 3359 ≤ 472 :=
  (smallCountTo3359).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3407 : oddPrimeCount 3407 = 478 :=
  smallPrimeAdvance 3359 48 472 6 smallCountTo3359 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3455 : oddPrimeCount 3455 = 481 :=
  smallPrimeAdvance 3407 48 478 3 smallCountTo3407 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3503 : oddPrimeCount 3503 = 488 :=
  smallPrimeAdvance 3455 48 481 7 smallCountTo3455 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3545 : oddPrimeCount 3545 = 495 :=
  smallPrimeAdvance 3503 42 488 7 smallCountTo3503 (by decide +kernel)

theorem base_3545 : oddPrimeCount 3545 ≤ 495 :=
  (smallCountTo3545).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3593 : oddPrimeCount 3593 = 502 :=
  smallPrimeAdvance 3545 48 495 7 smallCountTo3545 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3641 : oddPrimeCount 3641 = 508 :=
  smallPrimeAdvance 3593 48 502 6 smallCountTo3593 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3689 : oddPrimeCount 3689 = 513 :=
  smallPrimeAdvance 3641 48 508 5 smallCountTo3641 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3737 : oddPrimeCount 3737 = 520 :=
  smallPrimeAdvance 3689 48 513 7 smallCountTo3689 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3767 : oddPrimeCount 3767 = 523 :=
  smallPrimeAdvance 3737 30 520 3 smallCountTo3737 (by decide +kernel)

theorem base_3767 : oddPrimeCount 3767 ≤ 523 :=
  (smallCountTo3767).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3815 : oddPrimeCount 3815 = 528 :=
  smallPrimeAdvance 3767 48 523 5 smallCountTo3767 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3863 : oddPrimeCount 3863 = 535 :=
  smallPrimeAdvance 3815 48 528 7 smallCountTo3815 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3911 : oddPrimeCount 3911 = 540 :=
  smallPrimeAdvance 3863 48 535 5 smallCountTo3863 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo3959 : oddPrimeCount 3959 = 547 :=
  smallPrimeAdvance 3911 48 540 7 smallCountTo3911 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4007 : oddPrimeCount 4007 = 552 :=
  smallPrimeAdvance 3959 48 547 5 smallCountTo3959 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4025 : oddPrimeCount 4025 = 555 :=
  smallPrimeAdvance 4007 18 552 3 smallCountTo4007 (by decide +kernel)

theorem base_4025 : oddPrimeCount 4025 ≤ 555 :=
  (smallCountTo4025).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4073 : oddPrimeCount 4073 = 560 :=
  smallPrimeAdvance 4025 48 555 5 smallCountTo4025 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4095 : oddPrimeCount 4095 = 563 :=
  smallPrimeAdvance 4073 22 560 3 smallCountTo4073 (by decide +kernel)

theorem base_4095 : oddPrimeCount 4095 ≤ 563 :=
  (smallCountTo4095).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4143 : oddPrimeCount 4143 = 569 :=
  smallPrimeAdvance 4095 48 563 6 smallCountTo4095 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4151 : oddPrimeCount 4151 = 569 :=
  smallPrimeAdvance 4143 8 569 0 smallCountTo4143 (by decide +kernel)

theorem base_4151 : oddPrimeCount 4151 ≤ 569 :=
  (smallCountTo4151).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4199 : oddPrimeCount 4199 = 573 :=
  smallPrimeAdvance 4151 48 569 4 smallCountTo4151 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4227 : oddPrimeCount 4227 = 577 :=
  smallPrimeAdvance 4199 28 573 4 smallCountTo4199 (by decide +kernel)

theorem base_4227 : oddPrimeCount 4227 ≤ 577 :=
  (smallCountTo4227).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4275 : oddPrimeCount 4275 = 586 :=
  smallPrimeAdvance 4227 48 577 9 smallCountTo4227 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4287 : oddPrimeCount 4287 = 587 :=
  smallPrimeAdvance 4275 12 586 1 smallCountTo4275 (by decide +kernel)

theorem base_4287 : oddPrimeCount 4287 ≤ 587 :=
  (smallCountTo4287).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4335 : oddPrimeCount 4335 = 590 :=
  smallPrimeAdvance 4287 48 587 3 smallCountTo4287 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4383 : oddPrimeCount 4383 = 596 :=
  smallPrimeAdvance 4335 48 590 6 smallCountTo4335 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4389 : oddPrimeCount 4389 = 596 :=
  smallPrimeAdvance 4383 6 596 0 smallCountTo4383 (by decide +kernel)

theorem base_4389 : oddPrimeCount 4389 ≤ 596 :=
  (smallCountTo4389).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4437 : oddPrimeCount 4437 = 601 :=
  smallPrimeAdvance 4389 48 596 5 smallCountTo4389 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4485 : oddPrimeCount 4485 = 608 :=
  smallPrimeAdvance 4437 48 601 7 smallCountTo4437 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4511 : oddPrimeCount 4511 = 610 :=
  smallPrimeAdvance 4485 26 608 2 smallCountTo4485 (by decide +kernel)

theorem base_4511 : oddPrimeCount 4511 ≤ 610 :=
  (smallCountTo4511).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4559 : oddPrimeCount 4559 = 616 :=
  smallPrimeAdvance 4511 48 610 6 smallCountTo4511 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4607 : oddPrimeCount 4607 = 622 :=
  smallPrimeAdvance 4559 48 616 6 smallCountTo4559 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4649 : oddPrimeCount 4649 = 627 :=
  smallPrimeAdvance 4607 42 622 5 smallCountTo4607 (by decide +kernel)

theorem base_4649 : oddPrimeCount 4649 ≤ 627 :=
  (smallCountTo4649).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4697 : oddPrimeCount 4697 = 633 :=
  smallPrimeAdvance 4649 48 627 6 smallCountTo4649 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4745 : oddPrimeCount 4745 = 638 :=
  smallPrimeAdvance 4697 48 633 5 smallCountTo4697 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4793 : oddPrimeCount 4793 = 644 :=
  smallPrimeAdvance 4745 48 638 6 smallCountTo4745 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4811 : oddPrimeCount 4811 = 646 :=
  smallPrimeAdvance 4793 18 644 2 smallCountTo4793 (by decide +kernel)

theorem base_4811 : oddPrimeCount 4811 ≤ 646 :=
  (smallCountTo4811).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4859 : oddPrimeCount 4859 = 649 :=
  smallPrimeAdvance 4811 48 646 3 smallCountTo4811 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4907 : oddPrimeCount 4907 = 654 :=
  smallPrimeAdvance 4859 48 649 5 smallCountTo4859 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo4955 : oddPrimeCount 4955 = 661 :=
  smallPrimeAdvance 4907 48 654 7 smallCountTo4907 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5001 : oddPrimeCount 5001 = 668 :=
  smallPrimeAdvance 4955 46 661 7 smallCountTo4955 (by decide +kernel)

theorem base_5001 : oddPrimeCount 5001 ≤ 668 :=
  (smallCountTo5001).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5049 : oddPrimeCount 5049 = 674 :=
  smallPrimeAdvance 5001 48 668 6 smallCountTo5001 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5097 : oddPrimeCount 5097 = 679 :=
  smallPrimeAdvance 5049 48 674 5 smallCountTo5049 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5145 : oddPrimeCount 5145 = 684 :=
  smallPrimeAdvance 5097 48 679 5 smallCountTo5097 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5193 : oddPrimeCount 5193 = 690 :=
  smallPrimeAdvance 5145 48 684 6 smallCountTo5145 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5235 : oddPrimeCount 5235 = 695 :=
  smallPrimeAdvance 5193 42 690 5 smallCountTo5193 (by decide +kernel)

theorem base_5235 : oddPrimeCount 5235 ≤ 695 :=
  (smallCountTo5235).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5283 : oddPrimeCount 5283 = 700 :=
  smallPrimeAdvance 5235 48 695 5 smallCountTo5235 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5331 : oddPrimeCount 5331 = 704 :=
  smallPrimeAdvance 5283 48 700 4 smallCountTo5283 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5379 : oddPrimeCount 5379 = 707 :=
  smallPrimeAdvance 5331 48 704 3 smallCountTo5331 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5427 : oddPrimeCount 5427 = 715 :=
  smallPrimeAdvance 5379 48 707 8 smallCountTo5379 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5475 : oddPrimeCount 5475 = 721 :=
  smallPrimeAdvance 5427 48 715 6 smallCountTo5427 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5517 : oddPrimeCount 5517 = 727 :=
  smallPrimeAdvance 5475 42 721 6 smallCountTo5475 (by decide +kernel)

theorem base_5517 : oddPrimeCount 5517 ≤ 727 :=
  (smallCountTo5517).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5565 : oddPrimeCount 5565 = 733 :=
  smallPrimeAdvance 5517 48 727 6 smallCountTo5517 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5613 : oddPrimeCount 5613 = 737 :=
  smallPrimeAdvance 5565 48 733 4 smallCountTo5565 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5661 : oddPrimeCount 5661 = 745 :=
  smallPrimeAdvance 5613 48 737 8 smallCountTo5613 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5709 : oddPrimeCount 5709 = 750 :=
  smallPrimeAdvance 5661 48 745 5 smallCountTo5661 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5757 : oddPrimeCount 5757 = 756 :=
  smallPrimeAdvance 5709 48 750 6 smallCountTo5709 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5805 : oddPrimeCount 5805 = 760 :=
  smallPrimeAdvance 5757 48 756 4 smallCountTo5757 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5849 : oddPrimeCount 5849 = 767 :=
  smallPrimeAdvance 5805 44 760 7 smallCountTo5805 (by decide +kernel)

theorem base_5849 : oddPrimeCount 5849 ≤ 767 :=
  (smallCountTo5849).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5897 : oddPrimeCount 5897 = 775 :=
  smallPrimeAdvance 5849 48 767 8 smallCountTo5849 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5945 : oddPrimeCount 5945 = 779 :=
  smallPrimeAdvance 5897 48 775 4 smallCountTo5897 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo5993 : oddPrimeCount 5993 = 782 :=
  smallPrimeAdvance 5945 48 779 3 smallCountTo5945 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6041 : oddPrimeCount 6041 = 786 :=
  smallPrimeAdvance 5993 48 782 4 smallCountTo5993 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6089 : oddPrimeCount 6089 = 793 :=
  smallPrimeAdvance 6041 48 786 7 smallCountTo6041 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6137 : oddPrimeCount 6137 = 799 :=
  smallPrimeAdvance 6089 48 793 6 smallCountTo6089 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6185 : oddPrimeCount 6185 = 803 :=
  smallPrimeAdvance 6137 48 799 4 smallCountTo6137 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6233 : oddPrimeCount 6233 = 810 :=
  smallPrimeAdvance 6185 48 803 7 smallCountTo6185 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6267 : oddPrimeCount 6267 = 813 :=
  smallPrimeAdvance 6233 34 810 3 smallCountTo6233 (by decide +kernel)

theorem base_6267 : oddPrimeCount 6267 ≤ 813 :=
  (smallCountTo6267).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6315 : oddPrimeCount 6315 = 820 :=
  smallPrimeAdvance 6267 48 813 7 smallCountTo6267 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6363 : oddPrimeCount 6363 = 828 :=
  smallPrimeAdvance 6315 48 820 8 smallCountTo6315 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6411 : oddPrimeCount 6411 = 833 :=
  smallPrimeAdvance 6363 48 828 5 smallCountTo6363 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6459 : oddPrimeCount 6459 = 837 :=
  smallPrimeAdvance 6411 48 833 4 smallCountTo6411 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6507 : oddPrimeCount 6507 = 841 :=
  smallPrimeAdvance 6459 48 837 4 smallCountTo6459 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6555 : oddPrimeCount 6555 = 846 :=
  smallPrimeAdvance 6507 48 841 5 smallCountTo6507 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6603 : oddPrimeCount 6603 = 852 :=
  smallPrimeAdvance 6555 48 846 6 smallCountTo6555 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6651 : oddPrimeCount 6651 = 855 :=
  smallPrimeAdvance 6603 48 852 3 smallCountTo6603 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6699 : oddPrimeCount 6699 = 862 :=
  smallPrimeAdvance 6651 48 855 7 smallCountTo6651 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6747 : oddPrimeCount 6747 = 868 :=
  smallPrimeAdvance 6699 48 862 6 smallCountTo6699 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6779 : oddPrimeCount 6779 = 871 :=
  smallPrimeAdvance 6747 32 868 3 smallCountTo6747 (by decide +kernel)

theorem base_6779 : oddPrimeCount 6779 ≤ 871 :=
  (smallCountTo6779).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6827 : oddPrimeCount 6827 = 877 :=
  smallPrimeAdvance 6779 48 871 6 smallCountTo6779 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6875 : oddPrimeCount 6875 = 884 :=
  smallPrimeAdvance 6827 48 877 7 smallCountTo6827 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6923 : oddPrimeCount 6923 = 889 :=
  smallPrimeAdvance 6875 48 884 5 smallCountTo6875 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo6971 : oddPrimeCount 6971 = 895 :=
  smallPrimeAdvance 6923 48 889 6 smallCountTo6923 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7019 : oddPrimeCount 7019 = 902 :=
  smallPrimeAdvance 6971 48 895 7 smallCountTo6971 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7067 : oddPrimeCount 7067 = 906 :=
  smallPrimeAdvance 7019 48 902 4 smallCountTo7019 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7115 : oddPrimeCount 7115 = 910 :=
  smallPrimeAdvance 7067 48 906 4 smallCountTo7067 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7163 : oddPrimeCount 7163 = 915 :=
  smallPrimeAdvance 7115 48 910 5 smallCountTo7115 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7211 : oddPrimeCount 7211 = 920 :=
  smallPrimeAdvance 7163 48 915 5 smallCountTo7163 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7259 : oddPrimeCount 7259 = 927 :=
  smallPrimeAdvance 7211 48 920 7 smallCountTo7211 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7307 : oddPrimeCount 7307 = 930 :=
  smallPrimeAdvance 7259 48 927 3 smallCountTo7259 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7355 : oddPrimeCount 7355 = 936 :=
  smallPrimeAdvance 7307 48 930 6 smallCountTo7307 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7403 : oddPrimeCount 7403 = 938 :=
  smallPrimeAdvance 7355 48 936 2 smallCountTo7355 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7451 : oddPrimeCount 7451 = 942 :=
  smallPrimeAdvance 7403 48 938 4 smallCountTo7403 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7455 : oddPrimeCount 7455 = 942 :=
  smallPrimeAdvance 7451 4 942 0 smallCountTo7451 (by decide +kernel)

theorem base_7455 : oddPrimeCount 7455 ≤ 942 :=
  (smallCountTo7455).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7503 : oddPrimeCount 7503 = 949 :=
  smallPrimeAdvance 7455 48 942 7 smallCountTo7455 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7551 : oddPrimeCount 7551 = 957 :=
  smallPrimeAdvance 7503 48 949 8 smallCountTo7503 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7599 : oddPrimeCount 7599 = 964 :=
  smallPrimeAdvance 7551 48 957 7 smallCountTo7551 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7647 : oddPrimeCount 7647 = 969 :=
  smallPrimeAdvance 7599 48 964 5 smallCountTo7599 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7695 : oddPrimeCount 7695 = 975 :=
  smallPrimeAdvance 7647 48 969 6 smallCountTo7647 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7743 : oddPrimeCount 7743 = 981 :=
  smallPrimeAdvance 7695 48 975 6 smallCountTo7695 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7791 : oddPrimeCount 7791 = 985 :=
  smallPrimeAdvance 7743 48 981 4 smallCountTo7743 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7839 : oddPrimeCount 7839 = 989 :=
  smallPrimeAdvance 7791 48 985 4 smallCountTo7791 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7887 : oddPrimeCount 7887 = 996 :=
  smallPrimeAdvance 7839 48 989 7 smallCountTo7839 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7935 : oddPrimeCount 7935 = 1001 :=
  smallPrimeAdvance 7887 48 996 5 smallCountTo7887 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo7983 : oddPrimeCount 7983 = 1005 :=
  smallPrimeAdvance 7935 48 1001 4 smallCountTo7935 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8031 : oddPrimeCount 8031 = 1009 :=
  smallPrimeAdvance 7983 48 1005 4 smallCountTo7983 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8079 : oddPrimeCount 8079 = 1013 :=
  smallPrimeAdvance 8031 48 1009 4 smallCountTo8031 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8127 : oddPrimeCount 8127 = 1021 :=
  smallPrimeAdvance 8079 48 1013 8 smallCountTo8079 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8175 : oddPrimeCount 8175 = 1025 :=
  smallPrimeAdvance 8127 48 1021 4 smallCountTo8127 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8191 : oddPrimeCount 8191 = 1027 :=
  smallPrimeAdvance 8175 16 1025 2 smallCountTo8175 (by decide +kernel)

theorem base_8191 : oddPrimeCount 8191 ≤ 1027 :=
  (smallCountTo8191).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8239 : oddPrimeCount 8239 = 1033 :=
  smallPrimeAdvance 8191 48 1027 6 smallCountTo8191 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8287 : oddPrimeCount 8287 = 1038 :=
  smallPrimeAdvance 8239 48 1033 5 smallCountTo8239 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8335 : oddPrimeCount 8335 = 1044 :=
  smallPrimeAdvance 8287 48 1038 6 smallCountTo8287 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8383 : oddPrimeCount 8383 = 1048 :=
  smallPrimeAdvance 8335 48 1044 4 smallCountTo8335 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8431 : oddPrimeCount 8431 = 1054 :=
  smallPrimeAdvance 8383 48 1048 6 smallCountTo8383 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8479 : oddPrimeCount 8479 = 1058 :=
  smallPrimeAdvance 8431 48 1054 4 smallCountTo8431 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8527 : oddPrimeCount 8527 = 1062 :=
  smallPrimeAdvance 8479 48 1058 4 smallCountTo8479 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8575 : oddPrimeCount 8575 = 1067 :=
  smallPrimeAdvance 8527 48 1062 5 smallCountTo8527 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8623 : oddPrimeCount 8623 = 1072 :=
  smallPrimeAdvance 8575 48 1067 5 smallCountTo8575 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8671 : oddPrimeCount 8671 = 1078 :=
  smallPrimeAdvance 8623 48 1072 6 smallCountTo8623 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8719 : oddPrimeCount 8719 = 1086 :=
  smallPrimeAdvance 8671 48 1078 8 smallCountTo8671 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8767 : oddPrimeCount 8767 = 1092 :=
  smallPrimeAdvance 8719 48 1086 6 smallCountTo8719 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8815 : oddPrimeCount 8815 = 1096 :=
  smallPrimeAdvance 8767 48 1092 4 smallCountTo8767 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8863 : oddPrimeCount 8863 = 1104 :=
  smallPrimeAdvance 8815 48 1096 8 smallCountTo8815 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8885 : oddPrimeCount 8885 = 1105 :=
  smallPrimeAdvance 8863 22 1104 1 smallCountTo8863 (by decide +kernel)

theorem base_8885 : oddPrimeCount 8885 ≤ 1105 :=
  (smallCountTo8885).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8933 : oddPrimeCount 8933 = 1110 :=
  smallPrimeAdvance 8885 48 1105 5 smallCountTo8885 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo8981 : oddPrimeCount 8981 = 1115 :=
  smallPrimeAdvance 8933 48 1110 5 smallCountTo8933 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9029 : oddPrimeCount 9029 = 1121 :=
  smallPrimeAdvance 8981 48 1115 6 smallCountTo8981 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9077 : oddPrimeCount 9077 = 1126 :=
  smallPrimeAdvance 9029 48 1121 5 smallCountTo9029 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9125 : oddPrimeCount 9125 = 1129 :=
  smallPrimeAdvance 9077 48 1126 3 smallCountTo9077 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9173 : oddPrimeCount 9173 = 1136 :=
  smallPrimeAdvance 9125 48 1129 7 smallCountTo9125 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9221 : oddPrimeCount 9221 = 1142 :=
  smallPrimeAdvance 9173 48 1136 6 smallCountTo9173 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9269 : oddPrimeCount 9269 = 1146 :=
  smallPrimeAdvance 9221 48 1142 4 smallCountTo9221 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9317 : oddPrimeCount 9317 = 1151 :=
  smallPrimeAdvance 9269 48 1146 5 smallCountTo9269 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9365 : oddPrimeCount 9365 = 1157 :=
  smallPrimeAdvance 9317 48 1151 6 smallCountTo9317 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9413 : oddPrimeCount 9413 = 1163 :=
  smallPrimeAdvance 9365 48 1157 6 smallCountTo9365 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9461 : oddPrimeCount 9461 = 1170 :=
  smallPrimeAdvance 9413 48 1163 7 smallCountTo9413 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9509 : oddPrimeCount 9509 = 1176 :=
  smallPrimeAdvance 9461 48 1170 6 smallCountTo9461 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9557 : oddPrimeCount 9557 = 1182 :=
  smallPrimeAdvance 9509 48 1176 6 smallCountTo9509 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9605 : oddPrimeCount 9605 = 1184 :=
  smallPrimeAdvance 9557 48 1182 2 smallCountTo9557 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9653 : oddPrimeCount 9653 = 1191 :=
  smallPrimeAdvance 9605 48 1184 7 smallCountTo9605 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9701 : oddPrimeCount 9701 = 1196 :=
  smallPrimeAdvance 9653 48 1191 5 smallCountTo9653 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9737 : oddPrimeCount 9737 = 1199 :=
  smallPrimeAdvance 9701 36 1196 3 smallCountTo9701 (by decide +kernel)

theorem base_9737 : oddPrimeCount 9737 ≤ 1199 :=
  (smallCountTo9737).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9785 : oddPrimeCount 9785 = 1205 :=
  smallPrimeAdvance 9737 48 1199 6 smallCountTo9737 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9833 : oddPrimeCount 9833 = 1212 :=
  smallPrimeAdvance 9785 48 1205 7 smallCountTo9785 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9881 : oddPrimeCount 9881 = 1217 :=
  smallPrimeAdvance 9833 48 1212 5 smallCountTo9833 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9929 : oddPrimeCount 9929 = 1223 :=
  smallPrimeAdvance 9881 48 1217 6 smallCountTo9881 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo9977 : oddPrimeCount 9977 = 1228 :=
  smallPrimeAdvance 9929 48 1223 5 smallCountTo9929 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10025 : oddPrimeCount 10025 = 1230 :=
  smallPrimeAdvance 9977 48 1228 2 smallCountTo9977 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10073 : oddPrimeCount 10073 = 1235 :=
  smallPrimeAdvance 10025 48 1230 5 smallCountTo10025 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10121 : oddPrimeCount 10121 = 1241 :=
  smallPrimeAdvance 10073 48 1235 6 smallCountTo10073 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10169 : oddPrimeCount 10169 = 1248 :=
  smallPrimeAdvance 10121 48 1241 7 smallCountTo10121 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10217 : oddPrimeCount 10217 = 1252 :=
  smallPrimeAdvance 10169 48 1248 4 smallCountTo10169 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10265 : oddPrimeCount 10265 = 1257 :=
  smallPrimeAdvance 10217 48 1252 5 smallCountTo10217 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10313 : oddPrimeCount 10313 = 1264 :=
  smallPrimeAdvance 10265 48 1257 7 smallCountTo10265 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10361 : oddPrimeCount 10361 = 1270 :=
  smallPrimeAdvance 10313 48 1264 6 smallCountTo10313 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10409 : oddPrimeCount 10409 = 1273 :=
  smallPrimeAdvance 10361 48 1270 3 smallCountTo10361 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10457 : oddPrimeCount 10457 = 1278 :=
  smallPrimeAdvance 10409 48 1273 5 smallCountTo10409 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10505 : oddPrimeCount 10505 = 1284 :=
  smallPrimeAdvance 10457 48 1278 6 smallCountTo10457 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10553 : oddPrimeCount 10553 = 1287 :=
  smallPrimeAdvance 10505 48 1284 3 smallCountTo10505 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10601 : oddPrimeCount 10601 = 1292 :=
  smallPrimeAdvance 10553 48 1287 5 smallCountTo10553 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10649 : oddPrimeCount 10649 = 1297 :=
  smallPrimeAdvance 10601 48 1292 5 smallCountTo10601 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10697 : oddPrimeCount 10697 = 1303 :=
  smallPrimeAdvance 10649 48 1297 6 smallCountTo10649 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10745 : oddPrimeCount 10745 = 1309 :=
  smallPrimeAdvance 10697 48 1303 6 smallCountTo10697 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10793 : oddPrimeCount 10793 = 1313 :=
  smallPrimeAdvance 10745 48 1309 4 smallCountTo10745 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10829 : oddPrimeCount 10829 = 1314 :=
  smallPrimeAdvance 10793 36 1313 1 smallCountTo10793 (by decide +kernel)

theorem base_10829 : oddPrimeCount 10829 ≤ 1314 :=
  (smallCountTo10829).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10877 : oddPrimeCount 10877 = 1321 :=
  smallPrimeAdvance 10829 48 1314 7 smallCountTo10829 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10925 : oddPrimeCount 10925 = 1326 :=
  smallPrimeAdvance 10877 48 1321 5 smallCountTo10877 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo10973 : oddPrimeCount 10973 = 1331 :=
  smallPrimeAdvance 10925 48 1326 5 smallCountTo10925 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11021 : oddPrimeCount 11021 = 1335 :=
  smallPrimeAdvance 10973 48 1331 4 smallCountTo10973 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11069 : oddPrimeCount 11069 = 1340 :=
  smallPrimeAdvance 11021 48 1335 5 smallCountTo11021 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11117 : oddPrimeCount 11117 = 1346 :=
  smallPrimeAdvance 11069 48 1340 6 smallCountTo11069 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11165 : oddPrimeCount 11165 = 1351 :=
  smallPrimeAdvance 11117 48 1346 5 smallCountTo11117 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11213 : oddPrimeCount 11213 = 1356 :=
  smallPrimeAdvance 11165 48 1351 5 smallCountTo11165 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11261 : oddPrimeCount 11261 = 1361 :=
  smallPrimeAdvance 11213 48 1356 5 smallCountTo11213 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11309 : oddPrimeCount 11309 = 1365 :=
  smallPrimeAdvance 11261 48 1361 4 smallCountTo11261 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11357 : oddPrimeCount 11357 = 1371 :=
  smallPrimeAdvance 11309 48 1365 6 smallCountTo11309 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11405 : oddPrimeCount 11405 = 1375 :=
  smallPrimeAdvance 11357 48 1371 4 smallCountTo11357 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11453 : oddPrimeCount 11453 = 1380 :=
  smallPrimeAdvance 11405 48 1375 5 smallCountTo11405 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11501 : oddPrimeCount 11501 = 1386 :=
  smallPrimeAdvance 11453 48 1380 6 smallCountTo11453 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11549 : oddPrimeCount 11549 = 1390 :=
  smallPrimeAdvance 11501 48 1386 4 smallCountTo11501 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11597 : oddPrimeCount 11597 = 1395 :=
  smallPrimeAdvance 11549 48 1390 5 smallCountTo11549 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11645 : oddPrimeCount 11645 = 1398 :=
  smallPrimeAdvance 11597 48 1395 3 smallCountTo11597 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11693 : oddPrimeCount 11693 = 1402 :=
  smallPrimeAdvance 11645 48 1398 4 smallCountTo11645 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11741 : oddPrimeCount 11741 = 1407 :=
  smallPrimeAdvance 11693 48 1402 5 smallCountTo11693 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11789 : oddPrimeCount 11789 = 1412 :=
  smallPrimeAdvance 11741 48 1407 5 smallCountTo11741 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11837 : oddPrimeCount 11837 = 1419 :=
  smallPrimeAdvance 11789 48 1412 7 smallCountTo11789 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11885 : oddPrimeCount 11885 = 1422 :=
  smallPrimeAdvance 11837 48 1419 3 smallCountTo11837 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11933 : oddPrimeCount 11933 = 1429 :=
  smallPrimeAdvance 11885 48 1422 7 smallCountTo11885 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo11981 : oddPrimeCount 11981 = 1436 :=
  smallPrimeAdvance 11933 48 1429 7 smallCountTo11933 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12029 : oddPrimeCount 12029 = 1439 :=
  smallPrimeAdvance 11981 48 1436 3 smallCountTo11981 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12077 : oddPrimeCount 12077 = 1445 :=
  smallPrimeAdvance 12029 48 1439 6 smallCountTo12029 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12125 : oddPrimeCount 12125 = 1451 :=
  smallPrimeAdvance 12077 48 1445 6 smallCountTo12077 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12173 : oddPrimeCount 12173 = 1456 :=
  smallPrimeAdvance 12125 48 1451 5 smallCountTo12125 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12221 : oddPrimeCount 12221 = 1459 :=
  smallPrimeAdvance 12173 48 1456 3 smallCountTo12173 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12249 : oddPrimeCount 12249 = 1462 :=
  smallPrimeAdvance 12221 28 1459 3 smallCountTo12221 (by decide +kernel)

theorem base_12249 : oddPrimeCount 12249 ≤ 1462 :=
  (smallCountTo12249).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12297 : oddPrimeCount 12297 = 1469 :=
  smallPrimeAdvance 12249 48 1462 7 smallCountTo12249 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12345 : oddPrimeCount 12345 = 1473 :=
  smallPrimeAdvance 12297 48 1469 4 smallCountTo12297 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12393 : oddPrimeCount 12393 = 1478 :=
  smallPrimeAdvance 12345 48 1473 5 smallCountTo12345 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12441 : oddPrimeCount 12441 = 1484 :=
  smallPrimeAdvance 12393 48 1478 6 smallCountTo12393 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12489 : oddPrimeCount 12489 = 1489 :=
  smallPrimeAdvance 12441 48 1484 5 smallCountTo12441 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12537 : oddPrimeCount 12537 = 1495 :=
  smallPrimeAdvance 12489 48 1489 6 smallCountTo12489 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12585 : oddPrimeCount 12585 = 1502 :=
  smallPrimeAdvance 12537 48 1495 7 smallCountTo12537 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12633 : oddPrimeCount 12633 = 1507 :=
  smallPrimeAdvance 12585 48 1502 5 smallCountTo12585 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12681 : oddPrimeCount 12681 = 1513 :=
  smallPrimeAdvance 12633 48 1507 6 smallCountTo12633 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12729 : oddPrimeCount 12729 = 1518 :=
  smallPrimeAdvance 12681 48 1513 5 smallCountTo12681 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12777 : oddPrimeCount 12777 = 1522 :=
  smallPrimeAdvance 12729 48 1518 4 smallCountTo12729 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12825 : oddPrimeCount 12825 = 1528 :=
  smallPrimeAdvance 12777 48 1522 6 smallCountTo12777 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12873 : oddPrimeCount 12873 = 1531 :=
  smallPrimeAdvance 12825 48 1528 3 smallCountTo12825 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12921 : oddPrimeCount 12921 = 1538 :=
  smallPrimeAdvance 12873 48 1531 7 smallCountTo12873 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo12969 : oddPrimeCount 12969 = 1543 :=
  smallPrimeAdvance 12921 48 1538 5 smallCountTo12921 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13017 : oddPrimeCount 13017 = 1550 :=
  smallPrimeAdvance 12969 48 1543 7 smallCountTo12969 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13065 : oddPrimeCount 13065 = 1555 :=
  smallPrimeAdvance 13017 48 1550 5 smallCountTo13017 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13113 : oddPrimeCount 13113 = 1559 :=
  smallPrimeAdvance 13065 48 1555 4 smallCountTo13065 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13161 : oddPrimeCount 13161 = 1564 :=
  smallPrimeAdvance 13113 48 1559 5 smallCountTo13113 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13209 : oddPrimeCount 13209 = 1569 :=
  smallPrimeAdvance 13161 48 1564 5 smallCountTo13161 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13257 : oddPrimeCount 13257 = 1574 :=
  smallPrimeAdvance 13209 48 1569 5 smallCountTo13209 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13305 : oddPrimeCount 13305 = 1578 :=
  smallPrimeAdvance 13257 48 1574 4 smallCountTo13257 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13353 : oddPrimeCount 13353 = 1584 :=
  smallPrimeAdvance 13305 48 1578 6 smallCountTo13305 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13401 : oddPrimeCount 13401 = 1588 :=
  smallPrimeAdvance 13353 48 1584 4 smallCountTo13353 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13449 : oddPrimeCount 13449 = 1592 :=
  smallPrimeAdvance 13401 48 1588 4 smallCountTo13401 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13497 : oddPrimeCount 13497 = 1598 :=
  smallPrimeAdvance 13449 48 1592 6 smallCountTo13449 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13545 : oddPrimeCount 13545 = 1602 :=
  smallPrimeAdvance 13497 48 1598 4 smallCountTo13497 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13593 : oddPrimeCount 13593 = 1606 :=
  smallPrimeAdvance 13545 48 1602 4 smallCountTo13545 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13641 : oddPrimeCount 13641 = 1611 :=
  smallPrimeAdvance 13593 48 1606 5 smallCountTo13593 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13689 : oddPrimeCount 13689 = 1616 :=
  smallPrimeAdvance 13641 48 1611 5 smallCountTo13641 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13737 : oddPrimeCount 13737 = 1624 :=
  smallPrimeAdvance 13689 48 1616 8 smallCountTo13689 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13785 : oddPrimeCount 13785 = 1629 :=
  smallPrimeAdvance 13737 48 1624 5 smallCountTo13737 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13833 : oddPrimeCount 13833 = 1634 :=
  smallPrimeAdvance 13785 48 1629 5 smallCountTo13785 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13881 : oddPrimeCount 13881 = 1639 :=
  smallPrimeAdvance 13833 48 1634 5 smallCountTo13833 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13929 : oddPrimeCount 13929 = 1645 :=
  smallPrimeAdvance 13881 48 1639 6 smallCountTo13881 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo13977 : oddPrimeCount 13977 = 1649 :=
  smallPrimeAdvance 13929 48 1645 4 smallCountTo13929 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14025 : oddPrimeCount 14025 = 1653 :=
  smallPrimeAdvance 13977 48 1649 4 smallCountTo13977 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14027 : oddPrimeCount 14027 = 1653 :=
  smallPrimeAdvance 14025 2 1653 0 smallCountTo14025 (by decide +kernel)

theorem base_14027 : oddPrimeCount 14027 ≤ 1653 :=
  (smallCountTo14027).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14075 : oddPrimeCount 14075 = 1658 :=
  smallPrimeAdvance 14027 48 1653 5 smallCountTo14027 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14123 : oddPrimeCount 14123 = 1662 :=
  smallPrimeAdvance 14075 48 1658 4 smallCountTo14075 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14171 : oddPrimeCount 14171 = 1666 :=
  smallPrimeAdvance 14123 48 1662 4 smallCountTo14123 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14219 : oddPrimeCount 14219 = 1670 :=
  smallPrimeAdvance 14171 48 1666 4 smallCountTo14171 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14267 : oddPrimeCount 14267 = 1674 :=
  smallPrimeAdvance 14219 48 1670 4 smallCountTo14219 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14315 : oddPrimeCount 14315 = 1677 :=
  smallPrimeAdvance 14267 48 1674 3 smallCountTo14267 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14363 : oddPrimeCount 14363 = 1682 :=
  smallPrimeAdvance 14315 48 1677 5 smallCountTo14315 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14411 : oddPrimeCount 14411 = 1688 :=
  smallPrimeAdvance 14363 48 1682 6 smallCountTo14363 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14459 : oddPrimeCount 14459 = 1694 :=
  smallPrimeAdvance 14411 48 1688 6 smallCountTo14411 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14507 : oddPrimeCount 14507 = 1698 :=
  smallPrimeAdvance 14459 48 1694 4 smallCountTo14459 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14555 : oddPrimeCount 14555 = 1704 :=
  smallPrimeAdvance 14507 48 1698 6 smallCountTo14507 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14603 : oddPrimeCount 14603 = 1709 :=
  smallPrimeAdvance 14555 48 1704 5 smallCountTo14555 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14651 : oddPrimeCount 14651 = 1714 :=
  smallPrimeAdvance 14603 48 1709 5 smallCountTo14603 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14699 : oddPrimeCount 14699 = 1719 :=
  smallPrimeAdvance 14651 48 1714 5 smallCountTo14651 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14747 : oddPrimeCount 14747 = 1726 :=
  smallPrimeAdvance 14699 48 1719 7 smallCountTo14699 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14795 : oddPrimeCount 14795 = 1732 :=
  smallPrimeAdvance 14747 48 1726 6 smallCountTo14747 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14843 : oddPrimeCount 14843 = 1738 :=
  smallPrimeAdvance 14795 48 1732 6 smallCountTo14795 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14891 : oddPrimeCount 14891 = 1744 :=
  smallPrimeAdvance 14843 48 1738 6 smallCountTo14843 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14939 : oddPrimeCount 14939 = 1748 :=
  smallPrimeAdvance 14891 48 1744 4 smallCountTo14891 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo14987 : oddPrimeCount 14987 = 1753 :=
  smallPrimeAdvance 14939 48 1748 5 smallCountTo14939 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15035 : oddPrimeCount 15035 = 1756 :=
  smallPrimeAdvance 14987 48 1753 3 smallCountTo14987 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15083 : oddPrimeCount 15083 = 1761 :=
  smallPrimeAdvance 15035 48 1756 5 smallCountTo15035 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15131 : oddPrimeCount 15131 = 1766 :=
  smallPrimeAdvance 15083 48 1761 5 smallCountTo15083 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15179 : oddPrimeCount 15179 = 1771 :=
  smallPrimeAdvance 15131 48 1766 5 smallCountTo15131 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15227 : oddPrimeCount 15227 = 1776 :=
  smallPrimeAdvance 15179 48 1771 5 smallCountTo15179 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15275 : oddPrimeCount 15275 = 1782 :=
  smallPrimeAdvance 15227 48 1776 6 smallCountTo15227 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15323 : oddPrimeCount 15323 = 1789 :=
  smallPrimeAdvance 15275 48 1782 7 smallCountTo15275 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15371 : oddPrimeCount 15371 = 1794 :=
  smallPrimeAdvance 15323 48 1789 5 smallCountTo15323 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15419 : oddPrimeCount 15419 = 1800 :=
  smallPrimeAdvance 15371 48 1794 6 smallCountTo15371 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15467 : oddPrimeCount 15467 = 1806 :=
  smallPrimeAdvance 15419 48 1800 6 smallCountTo15419 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15515 : oddPrimeCount 15515 = 1810 :=
  smallPrimeAdvance 15467 48 1806 4 smallCountTo15467 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15563 : oddPrimeCount 15563 = 1814 :=
  smallPrimeAdvance 15515 48 1810 4 smallCountTo15515 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15611 : oddPrimeCount 15611 = 1819 :=
  smallPrimeAdvance 15563 48 1814 5 smallCountTo15563 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15659 : oddPrimeCount 15659 = 1825 :=
  smallPrimeAdvance 15611 48 1819 6 smallCountTo15611 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15707 : oddPrimeCount 15707 = 1830 :=
  smallPrimeAdvance 15659 48 1825 5 smallCountTo15659 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15755 : oddPrimeCount 15755 = 1836 :=
  smallPrimeAdvance 15707 48 1830 6 smallCountTo15707 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15803 : oddPrimeCount 15803 = 1843 :=
  smallPrimeAdvance 15755 48 1836 7 smallCountTo15755 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15851 : oddPrimeCount 15851 = 1846 :=
  smallPrimeAdvance 15803 48 1843 3 smallCountTo15803 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15899 : oddPrimeCount 15899 = 1851 :=
  smallPrimeAdvance 15851 48 1846 5 smallCountTo15851 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15947 : oddPrimeCount 15947 = 1857 :=
  smallPrimeAdvance 15899 48 1851 6 smallCountTo15899 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo15995 : oddPrimeCount 15995 = 1861 :=
  smallPrimeAdvance 15947 48 1857 4 smallCountTo15947 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16043 : oddPrimeCount 16043 = 1864 :=
  smallPrimeAdvance 15995 48 1861 3 smallCountTo15995 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16091 : oddPrimeCount 16091 = 1872 :=
  smallPrimeAdvance 16043 48 1864 8 smallCountTo16043 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16139 : oddPrimeCount 16139 = 1877 :=
  smallPrimeAdvance 16091 48 1872 5 smallCountTo16091 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16187 : oddPrimeCount 16187 = 1880 :=
  smallPrimeAdvance 16139 48 1877 3 smallCountTo16139 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16235 : oddPrimeCount 16235 = 1886 :=
  smallPrimeAdvance 16187 48 1880 6 smallCountTo16187 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16283 : oddPrimeCount 16283 = 1890 :=
  smallPrimeAdvance 16235 48 1886 4 smallCountTo16235 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16331 : oddPrimeCount 16331 = 1892 :=
  smallPrimeAdvance 16283 48 1890 2 smallCountTo16283 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16337 : oddPrimeCount 16337 = 1893 :=
  smallPrimeAdvance 16331 6 1892 1 smallCountTo16331 (by decide +kernel)

theorem base_16337 : oddPrimeCount 16337 ≤ 1893 :=
  (smallCountTo16337).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem smallCountTo16383 : oddPrimeCount 16383 = 1899 :=
  smallPrimeAdvance 16337 46 1893 6 smallCountTo16337 (by decide +kernel)

theorem base_16383 : oddPrimeCount 16383 ≤ 1899 :=
  (smallCountTo16383).le

end A085264.PrimeSeeds

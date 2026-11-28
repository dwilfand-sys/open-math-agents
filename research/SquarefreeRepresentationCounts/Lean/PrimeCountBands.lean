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

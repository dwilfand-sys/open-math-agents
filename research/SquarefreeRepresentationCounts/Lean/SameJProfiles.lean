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

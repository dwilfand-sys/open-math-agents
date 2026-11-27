import FormalConjectures.ErdosProblems.«423»

open Finset BigOperators Filter

namespace HofstadterPrefix

def cumulative (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 n, a k

def blockValues (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (((Icc 1 m).product (Icc 1 m)).filter (fun q => q.1 < q.2)).image
    (fun q => ∑ k ∈ Icc q.1 q.2, a k)

theorem mem_blockValues {a : ℕ → ℕ} {m s : ℕ} :
    s ∈ blockValues a m ↔ Erdos423.IsConsecutiveBlockSum a (m + 1) s := by
  unfold blockValues Erdos423.IsConsecutiveBlockSum
  constructor
  · intro hs
    obtain ⟨⟨i, j⟩, hij, hsum⟩ := mem_image.mp hs
    obtain ⟨hij, hlt⟩ := mem_filter.mp hij
    obtain ⟨hi, hj⟩ := mem_product.mp hij
    obtain ⟨hi1, _⟩ := mem_Icc.mp hi
    obtain ⟨_, hjm⟩ := mem_Icc.mp hj
    exact ⟨i, j, hi1, by omega, by omega, hsum.symm⟩
  · rintro ⟨i, j, hi, hij, hjm, hs⟩
    refine mem_image.mpr ⟨(i, j), mem_filter.mpr ⟨?_, ?_⟩, hs.symm⟩
    · exact mem_product.mpr ⟨mem_Icc.mpr ⟨hi, by omega⟩,
        mem_Icc.mpr ⟨by omega, by omega⟩⟩
    · change i < j
      omega

theorem ncard_blocks (a : ℕ → ℕ) (m : ℕ) :
    ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard =
      (blockValues a m).card := by
  have hset : {s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s} =
      (↑(blockValues a m) : Set ℕ) := by
    ext s
    exact mem_blockValues.symm
  simp [hset]

theorem cumulative_split (a : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    cumulative a j = cumulative a i + ∑ k ∈ Icc (i + 1) j, a k := by
  have hinterval : Icc 1 j = Icc 1 i ∪ Icc (i + 1) j := by
    ext k
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc 1 i) (Icc (i + 1) j) := by
    apply disjoint_left.mpr
    intro k hk1 hk2
    have hki := (mem_Icc.mp hk1).2
    have hik := (mem_Icc.mp hk2).1
    omega
  unfold cumulative
  rw [hinterval, sum_union hdisj]

def signedDifferences (a : ℕ → ℕ) (m : ℕ) : Finset ℤ :=
  ((range (m + 1)).product (range (m + 1))).image
    (fun q => (cumulative a q.1 : ℤ) - (cumulative a q.2 : ℤ))

theorem card_signedDifferences (a : ℕ → ℕ) (m : ℕ) :
    (signedDifferences a m).card ≤ 1 + 2 *
      (m + ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard) := by
  classical
  let single := (Icc 1 m).image a
  let values := single ∪ blockValues a m
  let pos := values.image (fun s : ℕ => (s : ℤ))
  let negs := values.image (fun s : ℕ => -(s : ℤ))
  have hsegment : ∀ {i j : ℕ}, i < j → j ≤ m →
      ∃ s ∈ values, (cumulative a j : ℤ) = (cumulative a i : ℤ) + (s : ℤ) := by
    intro i j hij hjm
    let s := ∑ k ∈ Icc (i + 1) j, a k
    refine ⟨s, ?_, ?_⟩
    · apply mem_union.mpr
      by_cases hadj : i + 1 = j
      · left
        apply mem_image.mpr
        refine ⟨j, mem_Icc.mpr ⟨by omega, hjm⟩, ?_⟩
        simp [s, hadj]
      · right
        apply mem_blockValues.mpr
        exact ⟨i + 1, j, by omega, by omega, by omega, rfl⟩
    · exact_mod_cast cumulative_split a hij.le
  have hcover : signedDifferences a m ⊆ insert 0 (pos ∪ negs) := by
    intro x hx
    unfold signedDifferences at hx
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.mp hx
    obtain ⟨hi, hj⟩ := mem_product.mp hij
    have him : i ≤ m := by have := mem_range.mp hi; omega
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    rcases lt_trichotomy i j with hlt | heq | hgt
    · obtain ⟨s, hs, hd⟩ := hsegment hlt hjm
      apply mem_insert_of_mem
      apply mem_union_right
      exact mem_image.mpr ⟨s, hs, by change -(s : ℤ) = (cumulative a i : ℤ) - (cumulative a j : ℤ); omega⟩
    · subst j
      simp
    · obtain ⟨s, hs, hd⟩ := hsegment hgt him
      apply mem_insert_of_mem
      apply mem_union_left
      exact mem_image.mpr ⟨s, hs, by change (s : ℤ) = (cumulative a i : ℤ) - (cumulative a j : ℤ); omega⟩
  have hsingle : single.card ≤ m := by
    calc single.card ≤ (Icc 1 m).card := card_image_le
         _ = m := by rw [Nat.card_Icc]; omega
  have hv : values.card ≤ single.card + (blockValues a m).card := card_union_le _ _
  have hp : pos.card ≤ values.card := card_image_le
  have hn : negs.card ≤ values.card := card_image_le
  have hc := card_le_card hcover
  have hi := card_insert_le (0 : ℤ) (pos ∪ negs)
  have hu := card_union_le pos negs
  rw [ncard_blocks]
  omega

theorem cumulative_strict_from_one {a : ℕ → ℕ}
    (ha : StrictMono (fun k => a (k + 1))) :
    StrictMono (fun k => cumulative a (k + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hterm : a 1 < a (k + 2) := ha (show 0 < k + 1 by omega)
  have hsum := cumulative_split a (i := k + 1) (j := k + 2) (by omega)
  have hnext : cumulative a (k + 2) = cumulative a (k + 1) + a (k + 2) := by
    simpa using hsum
  change cumulative a (k + 1) < cumulative a (k + 2)
  omega

-- Exactly the prefixes ending at indices 2 through m are used here.
theorem card_blocks_ge {a : ℕ → ℕ} (ha : StrictMono (fun k => a (k + 1))) (m : ℕ) :
    m - 1 ≤ ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard := by
  have hmono : StrictMono (fun k => cumulative a (k + 2)) := by
    intro i j hij
    exact cumulative_strict_from_one ha (Nat.succ_lt_succ hij)
  have hsub : (range (m - 1)).image (fun k => cumulative a (k + 2)) ⊆ blockValues a m := by
    intro s hs
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hs
    have hkm := mem_range.mp hk
    apply mem_blockValues.mpr
    exact ⟨1, k + 2, by decide, by omega, by omega, rfl⟩
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ hmono.injective, card_range] at hcard
  rwa [ncard_blocks]

-- This constant bound transfers the difference-set estimate without an exponent loss.
theorem card_signedDifferences_le_seven {a : ℕ → ℕ}
    (ha : StrictMono (fun k => a (k + 1))) {m : ℕ} (hm : 2 ≤ m) :
    (signedDifferences a m).card ≤
      7 * ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard := by
  have hsize := card_blocks_ge ha m
  have hcover := card_signedDifferences a m
  omega

-- The sample p 0, ..., p (m-1) has exactly m entries when p is strictly increasing.
def sampleDifferences (p : ℕ → ℤ) (m : ℕ) : Finset ℤ :=
  ((range m).product (range m)).image (fun q => p q.1 - p q.2)

theorem shifted_sample_subset (a : ℕ → ℕ) (m : ℕ) :
    sampleDifferences (fun k => (cumulative a (k + 1) : ℤ)) m ⊆
      signedDifferences a m := by
  intro x hx
  unfold sampleDifferences at hx
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.mp hx
  obtain ⟨hi, hj⟩ := mem_product.mp hij
  have him := mem_range.mp hi
  have hjm := mem_range.mp hj
  unfold signedDifferences
  exact mem_image.mpr ⟨(i + 1, j + 1), mem_product.mpr
    ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, rfl⟩

end HofstadterPrefix

/-! An elementary lower bound of exponent 3/2 for the difference set
of a sequence with distinct consecutive gaps. The argument counts the
rank distances of translated adjacent pairs (Solymosi's method). -/

open Finset

namespace OMA.ElementaryDifferenceBound

def rank (D : Finset ℤ) (x : ℤ) : ℕ := (D.filter (· < x)).card

lemma rank_strict {D : Finset ℤ} {x y : ℤ} (hx : x ∈ D) (h : x < y) :
    rank D x < rank D y := by
  have hs : insert x (D.filter (· < x)) ⊆ D.filter (· < y) := by
    intro t ht
    rcases mem_insert.mp ht with rfl | htx
    · exact mem_filter.mpr ⟨hx,h⟩
    · exact mem_filter.mpr ⟨(mem_filter.mp htx).1, (mem_filter.mp htx).2.trans h⟩
  have hh := card_le_card hs
  rw [card_insert_of_notMem (by simp)] at hh
  exact hh

lemma rank_injective {D : Finset ℤ} {x y : ℤ} (hx : x ∈ D) (hy : y ∈ D)
    (he : rank D x = rank D y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact ((rank_strict hx h).ne he).elim
  · exact h
  · exact ((rank_strict hy h).ne he.symm).elim

lemma rank_lt_card {D : Finset ℤ} {x : ℤ} (hx : x ∈ D) : rank D x < D.card := by
  have hs : insert x (D.filter (· < x)) ⊆ D :=
    insert_subset hx (filter_subset _ _)
  have hh := card_le_card hs
  rw [card_insert_of_notMem (by simp)] at hh
  exact hh

lemma sum_gaps (r : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, r i ≤ r (i+1)) :
    ∑ i ∈ range n, (r (i+1) - r i) ≤ r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hlast := h n (by omega)
    have hold := ih fun i hi => h i (by omega)
    omega

def sample (f : ℕ → ℤ) (m : ℕ) : Finset ℤ :=
  ((range m) ×ˢ (range m)).image (fun z => f z.1 - f z.2)

-- For k²+1 terms there are at least k³/2 distinct differences.
theorem squareSample {f : ℕ → ℤ} (hf : StrictMono f)
    (hd : Function.Injective fun i => f (i+1) - f i) (k : ℕ) (hk : 0 < k) :
    k ^ 3 ≤ 2 * (sample f (k ^ 2 + 1)).card := by
  let n := k ^ 2
  let D := sample f (n+1)
  let E := range n ×ˢ range n
  let r := fun b i => rank D (f i - f b)
  let g := fun v : ℕ × ℕ => r v.1 (v.2+1) - r v.1 v.2
  let U := E.filter fun v => g v < k
  let V := E.filter fun v => ¬ g v < k
  have memD {b i : ℕ} (hb : b ≤ n) (hi : i ≤ n) : f i - f b ∈ D :=
    mem_image.mpr ⟨(i,b),mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,rfl⟩
  have bounds {b i : ℕ} (hb : b < n) (hi : i < n) : r b i < r b (i+1) :=
    rank_strict (memD hb.le hi.le) (sub_lt_sub_right (hf (Nat.lt_succ_self i)) _)
  have row (b : ℕ) (hb : b ∈ range n) :
      ∑ i ∈ range n, g (b,i) ≤ D.card := by
    have h := sum_gaps (r b) n (fun i hi => (bounds (mem_range.mp hb) hi).le)
    exact h.trans (rank_lt_card (memD (mem_range.mp hb).le le_rfl)).le
  have totalCost : ∑ v ∈ E, g v ≤ n * D.card := by
    calc
      _ = ∑ b ∈ range n, ∑ i ∈ range n, g (b,i) := sum_product ..
      _ ≤ ∑ _ ∈ range n, D.card := sum_le_sum row
      _ = _ := by simp
  have expensive : k * V.card ≤ n * D.card := by
    calc
      _ = ∑ _ ∈ V, k := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ V, g v := sum_le_sum fun v hv => Nat.le_of_not_gt (mem_filter.mp hv).2
      _ ≤ ∑ v ∈ E, g v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)
      _ ≤ _ := totalCost
  let key := fun v : ℕ × ℕ => (r v.1 v.2, g v)
  have short : U.card ≤ D.card * k := by
    rw [← card_range D.card, ← card_range k, ← card_product]
    apply card_le_card_of_injOn key
    · intro v hv
      obtain ⟨hv, hg⟩ := mem_filter.mp hv
      obtain ⟨hb,hi⟩ := mem_product.mp hv
      exact mem_product.mpr ⟨mem_range.mpr (rank_lt_card (memD
        (mem_range.mp hb).le (mem_range.mp hi).le)),mem_range.mpr hg⟩
    · rintro ⟨b,i⟩ hbi ⟨c,j⟩ hcj he
      obtain ⟨hb,hi⟩ := mem_product.mp (mem_filter.mp hbi).1
      obtain ⟨hc,hj⟩ := mem_product.mp (mem_filter.mp hcj).1
      have hb' := mem_range.mp hb
      have hi' := mem_range.mp hi
      have hc' := mem_range.mp hc
      have hj' := mem_range.mp hj
      have e₁ : r b i = r c j := congrArg Prod.fst he
      have e₂ : r b (i+1) - r b i = r c (j+1) - r c j := congrArg Prod.snd he
      have h₁ := bounds hb' hi'
      have h₂ := bounds hc' hj'
      have e₃ : r b (i+1) = r c (j+1) := by omega
      have eq₁ := rank_injective (memD hb'.le hi'.le) (memD hc'.le hj'.le) e₁
      have eq₂ := rank_injective (memD hb'.le (by omega : i+1 ≤ n))
        (memD hc'.le (by omega : j+1 ≤ n)) e₃
      have eij : i = j := hd (by change f (i+1) - f i = f (j+1) - f j; omega)
      subst j
      have ebc : b = c := hf.injective (by omega)
      simp [ebc]
  have split : U.card + V.card = n ^ 2 := by
    change (E.filter _).card + (E.filter _).card = _
    rw [card_filter_add_card_filter_not]
    simp [E, pow_two]
  have all : k * (n ^ 2) ≤ 2 * n * D.card := by
    rw [← split, Nat.mul_add]
    calc
      _ ≤ k * (D.card * k) + n * D.card :=
        Nat.add_le_add (Nat.mul_le_mul_left k short) expensive
      _ = _ := by dsimp [n]; ring
  have hn : 0 < n := pow_pos hk 2
  have hres : n * (k ^ 3) ≤ n * (2 * D.card) := by
    calc
      _ = k * n ^ 2 := by dsimp [n]; ring
      _ ≤ _ := all
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hres hn

theorem sampleMono (f : ℕ → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    sample f m ⊆ sample f n := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
  obtain ⟨h₁,h₂⟩ := mem_product.mp hw
  exact mem_image.mpr ⟨w,mem_product.mpr ⟨mem_range.mpr ((mem_range.mp h₁).trans_le hmn),
    mem_range.mpr ((mem_range.mp h₂).trans_le hmn)⟩, rfl⟩

theorem cubicBound {f : ℕ → ℤ} (hf : StrictMono f)
    (hd : Function.Injective fun i => f (i+1) - f i) {m : ℕ} (hm : 2 ≤ m) :
    m ^ 3 ≤ 256 * (sample f m).card ^ 2 := by
  let k := (m-1).sqrt
  have hk : 0 < k := Nat.sqrt_pos.mpr (by omega)
  have hlow : k ^ 2 ≤ m - 1 := Nat.sqrt_le' _
  have hupp : m - 1 < (k+1) ^ 2 := Nat.lt_succ_sqrt' _
  have h2 : (k+1) ^ 2 ≤ (2*k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm4 : m ≤ (2*k) ^ 2 := by omega
  have hs := squareSample hf hd k hk
  have hmono := card_le_card (sampleMono f (by omega : k^2+1 ≤ m))
  have hD : k ^ 3 ≤ 2 * (sample f m).card := by omega
  calc
    _ ≤ ((2*k) ^ 2) ^ 3 := Nat.pow_le_pow_left hm4 3
    _ = 64 * (k ^ 3) ^ 2 := by ring
    _ ≤ 64 * (2 * (sample f m).card) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 2)
    _ = _ := by ring

end OMA.ElementaryDifferenceBound

open Finset

namespace HofstadterPrefix

-- An unconditional superlinear lower bound for the distinct block sums:
-- their count is at least m^(3/2)/112, with no incidence estimate assumed.
theorem blockValuesCube {a : ℕ → ℕ} (ha : StrictMono fun k => a (k+1))
    {m : ℕ} (hm : 2 ≤ m) :
    m ^ 3 ≤ 12544 * ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m+1) s}).ncard ^ 2 := by
  let p : ℕ → ℤ := fun k => cumulative a (k+1)
  have hp : StrictMono p := by
    intro i j hij
    change (cumulative a (i+1) : ℤ) < (cumulative a (j+1) : ℤ)
    exact_mod_cast cumulative_strict_from_one ha hij
  have increment (k : ℕ) : p (k+1) - p k = a (k+2) := by
    have hs := cumulative_split a (i := k+1) (j := k+2) (by omega)
    have he : cumulative a (k+2) = cumulative a (k+1) + a (k+2) := by simpa using hs
    change (cumulative a (k+2) : ℤ) - (cumulative a (k+1) : ℤ) = (a (k+2) : ℤ)
    omega
  have hinj : Function.Injective fun i => p (i+1) - p i := by
    intro i j he
    change p (i+1) - p i = p (j+1) - p j at he
    rw [increment i, increment j] at he
    have h : a (i+2) = a (j+2) := by exact_mod_cast he
    have hij : i+1 = j+1 := ha.injective h
    omega
  have hD := OMA.ElementaryDifferenceBound.cubicBound hp hinj hm
  have hcard : (OMA.ElementaryDifferenceBound.sample p m).card ≤
      7 * ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m+1) s}).ncard :=
    (card_le_card (shifted_sample_subset a m)).trans (card_signedDifferences_le_seven ha hm)
  calc
    _ ≤ _ := hD
    _ ≤ 256 * (7 * ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m+1) s}).ncard) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcard 2)
    _ = _ := by ring

end HofstadterPrefix

open Filter

namespace HofstadterPrefix

theorem elementaryBlockExponent {a : ℕ → ℕ} (ha : StrictMono fun k => a (k + 1))
    {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) ^ ((3 : ℝ) / 2) ≤
      112 * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ) := by
  let B := ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard
  have hnat : m ^ 3 ≤ 12544 * B ^ 2 := blockValuesCube ha hm
  have hreal : (m : ℝ) ^ 3 ≤ 12544 * (B : ℝ) ^ 2 := by exact_mod_cast hnat
  change (m : ℝ) ^ ((3 : ℝ) / 2) ≤ 112 * (B : ℝ)
  apply (sq_le_sq₀ (Real.rpow_nonneg (Nat.cast_nonneg m) _) (by positivity)).mp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg m) ((3 : ℝ) / 2) 2]
  have e : ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = (3 : ℕ) := by norm_num
  rw [e, Real.rpow_natCast]
  calc
    _ ≤ 12544 * (B : ℝ) ^ 2 := hreal
    _ = _ := by ring

theorem elementaryBlockCountForTransfer {a : ℕ → ℕ} (ha : StrictMono fun k => a (k + 1))
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ ((3 : ℝ) / 2 - η) ≤
        C * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ) := by
  refine ⟨112, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  exact (Real.rpow_le_rpow_of_exponent_le hm1 (sub_le_self _ hη.le)).trans
    (elementaryBlockExponent ha hm)

end HofstadterPrefix

#print axioms HofstadterPrefix.blockValuesCube
#print axioms HofstadterPrefix.elementaryBlockCountForTransfer

import OMAStatements.S_oeis_a050446

/-!
# Exact enumeration and corrected word bijection for A050446

This development uses the reference statement only for its executable
definitions. The proofs never invoke the conjecture itself.

Source: https://oeis.org/A050446
Credit: @dwilfand-sys
-/

/-!
# The corrected word interpretation of OEIS A050446

The path has vertices `0, …, n`, edges `0, …, n - 1`, and one loop at
each vertex. Each loop contributes once to the local sum. A letter is
represented by a zero-based member of `Fin (m + 1)`; its printed value is
one greater. The word bound on printed letters is therefore `m + 2`.
-/

namespace A050446.Correction

/-- The total label of the ordinary path edges incident to vertex `v`. -/
def incident {n : ℕ} (e : Fin n → ℕ) (v : Fin (n + 1)) : ℕ :=
  (if h : 0 < v.val ∧ v.val - 1 < n then e ⟨v.val - 1, h.2⟩ else 0) +
    (if h : v.val < n then e ⟨v.val, h⟩ else 0)

/-- A nonnegative label on each edge and each vertex loop with common magic sum. -/
structure Magic (n m : ℕ) where
  edge : Fin n → ℕ
  loop : Fin (n + 1) → ℕ
  balance : ∀ v, loop v + incident edge v = m

/-- Words on the positive alphabet `1, …, m + 1`, stored one below the
printed letter. -/
structure Word (n m : ℕ) where
  letter : Fin n → Fin (m + 1)
  adjacent : ∀ i j : Fin n, j.val = i.val + 1 →
    (letter i).val + 1 + ((letter j).val + 1) ≤ m + 2

lemma adjacent_incident {n : ℕ} (e : Fin n → ℕ) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    incident e ⟨j.val, by omega⟩ = e i + e j := by
  have h : 0 < j.val ∧ j.val - 1 < n := by have := i.isLt; omega
  have hj := j.isLt
  simp only [incident, dif_pos h, dif_pos hj]
  have hi : (⟨j.val - 1, h.2⟩ : Fin n) = i := Fin.ext (by omega)
  rw [hi]

lemma Magic.edge_le {n m : ℕ} (a : Magic n m) (i : Fin n) : a.edge i ≤ m := by
  let v : Fin (n + 1) := ⟨i.val, by omega⟩
  have hb := a.balance v
  simp only [incident, v, dif_pos i.isLt] at hb
  omega

lemma Word.incident_le {n m : ℕ} (w : Word n m) (v : Fin (n + 1)) :
    incident (fun i => (w.letter i).val) v ≤ m := by
  unfold incident
  split
  · rename_i hl
    let i : Fin n := ⟨v.val - 1, hl.2⟩
    split
    · rename_i hr
      let j : Fin n := ⟨v.val, hr⟩
      have h := w.adjacent i j (by dsimp [i, j]; omega)
      change (w.letter i).val + (w.letter j).val ≤ m
      omega
    · have hi := (w.letter i).isLt
      change (w.letter i).val + 0 ≤ m
      omega
  · split
    · rename_i hr
      have hi := (w.letter ⟨v.val, hr⟩).isLt
      omega
    · omega

def toWord {n m : ℕ} (a : Magic n m) : Word n m where
  letter i := ⟨a.edge i, Nat.lt_succ_of_le (a.edge_le i)⟩
  adjacent i j hij := by
    have hb := a.balance ⟨j.val, by omega⟩
    rw [adjacent_incident a.edge i j hij] at hb
    change a.edge i + 1 + (a.edge j + 1) ≤ m + 2
    omega

def toMagic {n m : ℕ} (w : Word n m) : Magic n m where
  edge i := (w.letter i).val
  loop v := m - incident (fun i => (w.letter i).val) v
  balance v := Nat.sub_add_cancel (w.incident_le v)

lemma magic_ext {n m : ℕ} {a b : Magic n m} (h : a.edge = b.edge) : a = b := by
  obtain ⟨e, l, hl⟩ := a
  obtain ⟨f, k, hk⟩ := b
  change e = f at h
  subst f
  have he : l = k := funext fun v => by
    have hx := hl v
    have hy := hk v
    omega
  subst k
  rfl

lemma word_ext {n m : ℕ} {a b : Word n m} (h : a.letter = b.letter) : a = b := by
  obtain ⟨e, he⟩ := a
  obtain ⟨f, hf⟩ := b
  change e = f at h
  subst f
  rfl

/-- The ordinary path edges determine the word and all the vertex loop labels.
This also covers the empty word and its unique one-vertex labeling. -/
def magicEquivWord (n m : ℕ) : Magic n m ≃ Word n m where
  toFun := toWord
  invFun := toMagic
  left_inv a := magic_ext rfl
  right_inv w := word_ext (funext fun _ => Fin.ext rfl)

instance (n m : ℕ) : Finite (Word n m) :=
  Finite.of_injective (fun w : Word n m => w.letter) (fun _ _ h => word_ext h)

instance (n m : ℕ) : Finite (Magic n m) :=
  Finite.of_injective (magicEquivWord n m) (magicEquivWord n m).injective

theorem corrected_cardinality (n m : ℕ) :
    Nat.card (Magic n m) = Nat.card (Word n m) :=
  Nat.card_congr (magicEquivWord n m)

/-- Increasing the alphabet and its adjacency threshold preserves every word. -/
def widen {n m : ℕ} (w : Word n m) : Word n (m + 1) where
  letter i := (w.letter i).castSucc
  adjacent i j hij := by
    have h := w.adjacent i j hij
    change (w.letter i).val + 1 + ((w.letter j).val + 1) ≤ m + 1 + 2
    omega

lemma widen_injective {n m : ℕ} : Function.Injective (@widen n m) := by
  intro a b h
  apply word_ext
  funext i
  exact Fin.ext (congrArg (fun w : Word n (m + 1) => (w.letter i).val) h)

/-- The first letter uses the newly available value and all later letters are 1. -/
def newWord (n m : ℕ) : Word n (m + 1) where
  letter i := ⟨if i.val = 0 then m + 1 else 0, by split <;> omega⟩
  adjacent i j hij := by
    have hj : j.val ≠ 0 := by omega
    simp only [if_neg hj]
    split <;> omega

lemma widen_not_surjective {n m : ℕ} (hn : 0 < n) :
    ¬ Function.Surjective (@widen n m) := by
  intro hs
  obtain ⟨w, hw⟩ := hs (newWord n m)
  let z : Fin n := ⟨0, hn⟩
  have he := congrArg (fun u : Word n (m + 1) => (u.letter z).val) hw
  have he' : (w.letter z).val = m + 1 := by simpa [widen, newWord, z] using he
  have hlt := (w.letter z).isLt
  omega

/-- The indexing discrepancy gives a strict inequality for every positive
word length, across all consecutive alphabet sizes. -/
theorem strict_word_count {n m : ℕ} (hn : 0 < n) :
    Nat.card (Word n m) < Nat.card (Word n (m + 1)) := by
  classical
  letI := Fintype.ofFinite (Word n m)
  letI := Fintype.ofFinite (Word n (m + 1))
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_not_surjective (@widen n m)
      widen_injective (widen_not_surjective hn)

end A050446.Correction

namespace A050446.Correction

/-- The adjacent-pair filter on the stored labels expresses the pointwise bound on
the corresponding positive letters. -/
theorem wordOK_iff (w : List ℕ) (m : ℕ) :
    ((w.zip (w.drop 1)).all (fun pair => decide (pair.1 + pair.2 + 2 ≤ m + 2)) = true) ↔
      ∀ i j : Fin w.length, j.val = i.val + 1 →
        w[i.val] + 1 + (w[j.val] + 1) ≤ m + 2 := by
  rw [List.all_eq_true]
  constructor
  · intro h i j hij
    have hmem : (w[i.val], w[j.val]) ∈ w.zip (w.drop 1) := by
      apply List.mem_iff_getElem?.mpr
      refine ⟨i.val, List.getElem?_zip_eq_some.mpr ⟨?_, ?_⟩⟩
      · exact List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩
      · rw [List.getElem?_drop, show 1 + i.val = j.val by omega]
        exact List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
    have hp : w[i.val] + w[j.val] + 2 ≤ m + 2 := of_decide_eq_true (h _ hmem)
    omega
  · intro h pair hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨ha, hb⟩ := List.getElem?_zip_eq_some.mp hi
    rw [List.getElem?_drop, Nat.add_comm 1 i] at hb
    obtain ⟨hi0, ha0⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hi1, hb1⟩ := List.getElem?_eq_some_iff.mp hb
    have hp := h ⟨i, hi0⟩ ⟨i+1, hi1⟩ rfl
    change w[i] + 1 + (w[i+1] + 1) ≤ m + 2 at hp
    rw [ha0, hb1] at hp
    exact decide_eq_true_iff.mpr (by omega)

end A050446.Correction

/-! This section uses the source statement's `labelings` enumeration. -/
namespace A050446.Correction
open OMA.S_oeis_a050446

lemma list_mem_labelings {xs : List ℕ} {n size : ℕ} :
    xs ∈ labelings n size ↔ xs.length = n ∧ ∀ x ∈ xs, x < size := by
  induction n generalizing xs with
  | zero =>
    cases xs <;> simp [labelings]
  | succ n ih =>
    cases xs with
    | nil => simp [labelings]
    | cons x xs =>
      rw [labelings, List.mem_flatMap]
      constructor
      · rintro ⟨y, hy, hcons⟩
        obtain ⟨ys, hys, heq⟩ := List.mem_map.mp hcons
        obtain ⟨hyx, htail⟩ := List.cons.inj heq
        subst y
        subst ys
        obtain ⟨hlen, hbound⟩ := (ih (xs := xs)).mp hys
        exact ⟨by simp [hlen], List.forall_mem_cons.mpr ⟨List.mem_range.mp hy, hbound⟩⟩
      · rintro ⟨hlen, hbound⟩
        obtain ⟨hx, htail⟩ := List.forall_mem_cons.mp hbound
        refine ⟨x, List.mem_range.mpr hx, List.mem_map.mpr ⟨xs, ?_, rfl⟩⟩
        exact (ih (xs := xs)).mpr ⟨by simpa using hlen, htail⟩

lemma list_nodup_labelings (n size : ℕ) : (labelings n size).Nodup := by
  induction n with
  | zero => simp [labelings]
  | succ n ih =>
    rw [labelings, List.nodup_flatMap]
    constructor
    · intro x _
      exact ih.map (fun _ _ he => (List.cons.inj he).2)
    · apply (List.nodup_range (n := size)).imp
      intro x y hxy
      apply List.disjoint_left.mpr
      intro z hx hy
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hx
      obtain ⟨b, _, hb⟩ := List.mem_map.mp hy
      exact hxy (List.cons.inj (ha.trans hb.symm)).1

def entry (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

lemma entry_eq {xs : List ℕ} {i : ℕ} (hi : i < xs.length) :
    entry xs i = xs[i] := by simp [entry, List.getElem?_eq_getElem hi]

lemma entry_zero {xs : List ℕ} {i : ℕ} (hi : xs.length ≤ i) :
    entry xs i = 0 := by simp [entry, List.getElem?_eq_none hi]

lemma entry_ofFn {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    entry (List.ofFn f) i.val = f i := by
  rw [entry_eq (by simp)]
  simp

lemma list_entry_ext {a b : List ℕ} (hab : a.length = b.length)
    (h : ∀ i < a.length, entry a i = entry b i) : a = b := by
  apply List.ext_getElem hab
  intro i ha hb
  simpa only [entry_eq ha, entry_eq hb] using h i ha

def listIncident (edges : List ℕ) (v : ℕ) : ℕ :=
  (if v = 0 then 0 else entry edges (v - 1)) + entry edges v

lemma incident_eq_listIncident {edges : List ℕ} {n : ℕ}
    (hn : edges.length = n) (v : Fin (n + 1)) :
    incident (fun i : Fin n => entry edges i.val) v = listIncident edges v.val := by
  unfold incident listIncident
  by_cases hz : v.val = 0
  · by_cases hu : 0 < n
    · simp [hz, hu]
    · simp [hz, hu, entry_zero (by omega : edges.length ≤ 0)]
  · have hl : 0 < v.val ∧ v.val - 1 < n := by have := v.isLt; omega
    simp only [dif_pos hl, if_neg hz]
    split
    · rfl
    · rename_i hu
      rw [entry_zero (by omega : edges.length ≤ v.val)]

def sourceWords (n m : ℕ) : List (List ℕ) :=
  (labelings n (m + 1)).filter fun w =>
    (w.zip (w.drop 1)).all fun pair => decide (pair.1 + pair.2 + 2 ≤ m + 2)

lemma list_words_corrected_length (n m : ℕ) :
    (sourceWords n m).length = wordCount n (m + 1) := rfl

def sourceLoops (edges : List ℕ) (n m : ℕ) : List (List ℕ) :=
  (labelings (n + 1) (m + 1)).filter fun loops =>
    (List.range (n + 1)).all fun v =>
      decide (entry loops v + listIncident edges v = m)

lemma sourceLoops_mem {edges loops : List ℕ} {n m : ℕ} :
    loops ∈ sourceLoops edges n m ↔
      loops ∈ labelings (n + 1) (m + 1) ∧
        ∀ v < n + 1, entry loops v + listIncident edges v = m := by
  simp [sourceLoops]

lemma table_eq_sum_loop_lengths (n m : ℕ) :
    tableValue n m = ((labelings n (m + 1)).map fun e => (sourceLoops e n m).length).sum := by
  simp [tableValue, sourceLoops, List.length_flatMap, entry, listIncident, Nat.add_assoc]

def forcedLoops (edges : List ℕ) (n m : ℕ) : List ℕ :=
  List.ofFn fun v : Fin (n + 1) => m - listIncident edges v.val

lemma forced_entry (edges : List ℕ) {n m v : ℕ} (hv : v < n + 1) :
    entry (forcedLoops edges n m) v = m - listIncident edges v := by
  exact entry_ofFn _ ⟨v, hv⟩

lemma forced_labels (edges : List ℕ) (n m : ℕ) :
    forcedLoops edges n m ∈ labelings (n + 1) (m + 1) := by
  apply list_mem_labelings.mpr
  constructor
  · simp [forcedLoops]
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    change m - listIncident edges i.val = x at hi
    omega

lemma loop_length (edges : List ℕ) (n m : ℕ) :
    (sourceLoops edges n m).length =
      if ∀ v < n + 1, listIncident edges v ≤ m then 1 else 0 := by
  classical
  by_cases h : ∀ v < n + 1, listIncident edges v ≤ m
  · rw [if_pos h]
    have hmem : ∀ l, l ∈ sourceLoops edges n m ↔ l = forcedLoops edges n m := by
      intro l
      constructor
      · intro hl
        obtain ⟨hr, hb⟩ := sourceLoops_mem.mp hl
        have hlen := (list_mem_labelings.mp hr).1
        apply list_entry_ext (by simpa [forcedLoops] using hlen)
        intro v hv
        have hv' : v < n + 1 := by omega
        rw [forced_entry _ hv']
        have := hb v hv'
        omega
      · rintro rfl
        refine sourceLoops_mem.mpr ⟨forced_labels edges n m, ?_⟩
        intro v hv
        rw [forced_entry _ hv, Nat.sub_add_cancel (h v hv)]
    have hs : (sourceLoops edges n m).toFinset = {forcedLoops edges n m} := by
      ext l
      simpa only [List.mem_toFinset, Finset.mem_singleton] using hmem l
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (list_nodup_labelings (n + 1) (m + 1)) :
      (sourceLoops edges n m).Nodup), hs, Finset.card_singleton]
  · rw [if_neg h]
    have he : sourceLoops edges n m = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro l hl
      have hb := (sourceLoops_mem.mp hl).2
      apply h
      intro v hv
      have := hb v hv
      omega
    rw [he, List.length_nil]

def wordTest (xs : List ℕ) (m : ℕ) : Bool :=
  (xs.zip (xs.drop 1)).all fun pair => decide (pair.1 + pair.2 + 2 ≤ m + 2)

lemma wordTest_iff {xs : List ℕ} {n m : ℕ} (hl : xs.length = n) :
    wordTest xs m = true ↔
      ∀ i j : Fin n, j.val = i.val + 1 →
        entry xs i.val + 1 + (entry xs j.val + 1) ≤ m + 2 := by
  subst n
  rw [show wordTest xs m =
    (xs.zip (xs.drop 1)).all (fun t => decide (t.1 + t.2 + 2 ≤ m + 2)) by rfl,
    wordOK_iff]
  constructor <;> intro h i j hij
  · simpa only [entry_eq i.isLt, entry_eq j.isLt] using h i j hij
  · simpa only [entry_eq i.isLt, entry_eq j.isLt] using h i j hij

def sourceWordType (n m : ℕ) := {xs : List ℕ // xs ∈ (sourceWords n m).toFinset}

lemma source_bounds {xs : List ℕ} {n m : ℕ} (hx : xs ∈ labelings n (m + 1))
    (i : Fin n) : entry xs i.val < m + 1 := by
  obtain ⟨hl, hb⟩ := list_mem_labelings.mp hx
  have hi : i.val < xs.length := by have := i.isLt; omega
  rw [entry_eq hi]
  exact hb _ (List.getElem_mem hi)

def decodeWord {n m : ℕ} (xs : sourceWordType n m) : Word n m := by
  have h := List.mem_filter.mp (List.mem_toFinset.mp xs.property)
  have hr := h.1
  have hw := h.2
  have hl := (list_mem_labelings.mp hr).1
  exact {
    letter := fun i => ⟨entry xs.val i.val, source_bounds hr i⟩
    adjacent := (wordTest_iff hl).mp hw }

def encodeWord {n m : ℕ} (w : Word n m) : sourceWordType n m := by
  let xs := List.ofFn fun i : Fin n => (w.letter i).val
  have hl : xs.length = n := List.length_ofFn
  refine ⟨xs, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨?_, ?_⟩)⟩
  · refine list_mem_labelings.mpr ⟨hl, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    exact hi ▸ (w.letter i).isLt
  · apply (wordTest_iff hl).mpr
    intro i j hij
    change entry (List.ofFn _) i.val + 1 + (entry (List.ofFn _) j.val + 1) ≤ m + 2
    simpa only [entry_ofFn] using w.adjacent i j hij

def wordListEquiv (n m : ℕ) : Word n m ≃ sourceWordType n m where
  toFun := encodeWord
  invFun := decodeWord
  left_inv w := by
    apply word_ext
    funext i
    apply Fin.ext
    exact entry_ofFn (fun j => (w.letter j).val) i
  right_inv xs := by
    apply Subtype.ext
    obtain ⟨hlist, _⟩ := List.mem_filter.mp (List.mem_toFinset.mp xs.property)
    have hl := (list_mem_labelings.mp hlist).1
    apply list_entry_ext
    · change (List.ofFn _).length = xs.val.length
      simpa only [List.length_ofFn] using hl.symm
    · intro i hi
      change i < (List.ofFn (fun j : Fin n => entry xs.val j.val)).length at hi
      have hi' : i < n := by simpa only [List.length_ofFn] using hi
      exact entry_ofFn (fun j : Fin n => entry xs.val j.val) ⟨i, hi'⟩

theorem wordCount_card (n m : ℕ) :
    wordCount n (m + 1) = Nat.card (Word n m) := by
  rw [← Nat.card_congr (wordListEquiv n m).symm]
  change (sourceWords n m).length = Nat.card ↥((sourceWords n m).toFinset)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup]
  exact List.Nodup.filter _ (list_nodup_labelings n (m + 1))

lemma wordTest_iff_vertex {n m : ℕ} {e : List ℕ} (he : e ∈ labelings n (m + 1)) :
    wordTest e m = true ↔ ∀ v < n + 1, listIncident e v ≤ m := by
  have hl := (list_mem_labelings.mp he).1
  constructor
  · intro hw v hv
    let w : Word n m := {
      letter := fun i => ⟨entry e i.val, source_bounds he i⟩
      adjacent := (wordTest_iff hl).mp hw }
    have h := w.incident_le ⟨v, hv⟩
    change incident (fun i : Fin n => entry e i.val) ⟨v, hv⟩ ≤ m at h
    rwa [incident_eq_listIncident hl] at h
  · intro h
    apply (wordTest_iff hl).mpr
    intro i j hij
    let v : Fin (n + 1) := ⟨j.val, by omega⟩
    have h' : incident (fun t : Fin n => entry e t.val) v ≤ m := by
      rw [incident_eq_listIncident hl]
      exact h v.val v.isLt
    rw [adjacent_incident (fun t : Fin n => entry e t.val) i j hij] at h'
    omega

lemma sum_length_filter {α : Type*} (xs : List α) (f : α → ℕ) (p : α → Bool)
    (hf : ∀ x ∈ xs, f x = if p x then 1 else 0) :
    (xs.map f).sum = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    cases hp : p x <;> simp [hp, hh, ht, Nat.add_comm]

/-- The corrected bijection is valid for the exact list counts used by the source statement. -/
theorem corrected_source_counts (n m : ℕ) : tableValue n m = wordCount n (m + 1) := by
  classical
  rw [table_eq_sum_loop_lengths]
  apply sum_length_filter (labelings n (m + 1)) (fun e => (sourceLoops e n m).length)
    (fun e => wordTest e m)
  intro e he
  rw [loop_length, ← wordTest_iff_vertex he]

theorem tableValue_card (n m : ℕ) : tableValue n m = Nat.card (Magic n m) := by
  rw [corrected_source_counts, wordCount_card, corrected_cardinality]

/-- The literal alphabet size and threshold from the OEIS question, including
the empty alphabet. -/
def originalWords (n m : ℕ) : List (List ℕ) :=
  (labelings n m).filter fun w =>
    (w.zip (w.drop 1)).all fun pair => decide (pair.1 + pair.2 + 2 ≤ m + 1)

def OriginalWord (n m : ℕ) := ↥((originalWords n m).toFinset)

theorem original_word_count_card (n m : ℕ) :
    wordCount n m = Nat.card (OriginalWord n m) := by
  change (originalWords n m).length = Nat.card ↥((originalWords n m).toFinset)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup]
  exact List.Nodup.filter _ (list_nodup_labelings n m)

theorem original_claim_iff_cardinalities :
    (∀ n m : ℕ, tableValue n m = wordCount n m) ↔
      ∀ n m : ℕ, Nat.card (Magic n m) = Nat.card (OriginalWord n m) := by
  simp only [tableValue_card, original_word_count_card]

theorem strict_source_counts_succ {n : ℕ} (hn : 0 < n) (m : ℕ) :
    wordCount n (m + 1) < tableValue n (m + 1) := by
  rw [wordCount_card, tableValue_card, corrected_cardinality]
  exact strict_word_count hn

theorem zero_magic_count (n : ℕ) : tableValue n 0 = 1 := by
  rw [corrected_source_counts, wordCount_card]
  apply Nat.card_eq_one_iff_exists.mpr
  let w : Word n 0 := {
    letter := fun _ => 0
    adjacent := by intro i j _; norm_num }
  refine ⟨w, fun v => word_ext (funext fun i => ?_)⟩
  exact Subsingleton.elim _ _

theorem strict_source_counts {n : ℕ} (hn : 0 < n) (m : ℕ) :
    wordCount n m < tableValue n m := by
  cases m with
  | zero =>
    rw [zero_magic_count]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [wordCount, labelings]
  | succ m => exact strict_source_counts_succ hn m

/-- The equality from the OEIS question holds exactly on its zeroth row. -/
theorem source_equality_iff (n m : ℕ) :
    tableValue n m = wordCount n m ↔ n = 0 := by
  constructor
  · intro he
    by_contra hn
    exact (ne_of_lt (strict_source_counts (Nat.pos_of_ne_zero hn) m)) he.symm
  · rintro rfl
    rw [corrected_source_counts]
    simp [wordCount, labelings]

end A050446.Correction

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a050446.main) := by
  intro h
  have hlt := A050446.Correction.strict_source_counts_succ (n := 2) (by decide) 0
  exact (ne_of_lt hlt) (h 2 1).symm

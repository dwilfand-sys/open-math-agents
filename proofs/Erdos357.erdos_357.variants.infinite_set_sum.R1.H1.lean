import OMAReductions.R_Erdos357_erdos_357_variants_infinite_set_sum_R1
import Mathlib

/-!
# A sparse coarsening of a divergent reciprocal series

Credit: @dwilfand-sys. Codex developed the blocking argument and formalization.
The lemma applies to any positive strictly increasing sequence of integers.
-/

namespace Erdos357Coarsen

variable {α : Type*} [AddCommMonoid α]

def blockSum (a : ℕ → α) (cut : ℕ → ℕ) (j : ℕ) : α :=
  ∑ i ∈ Finset.Ico (cut j) (cut (j + 1)), a i

private theorem join_intervals (f : ℕ → α) {l m r : ℕ} (hlm : l ≤ m) (hmr : m ≤ r) :
    (∑ i ∈ Finset.Ico l m, f i) + (∑ i ∈ Finset.Ico m r, f i) =
      ∑ i ∈ Finset.Ico l r, f i := by
  have hdis : Disjoint (Finset.Ico l m) (Finset.Ico m r) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Nat.not_lt_of_ge (Finset.mem_Ico.mp hj).1) (Finset.mem_Ico.mp hi).2
  have hunion : Finset.Ico l m ∪ Finset.Ico m r = Finset.Ico l r := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← Finset.sum_union hdis, hunion]

theorem sum_shifted_range (a : ℕ → ℕ) (l k : ℕ) :
    (∑ i ∈ Finset.Ico l (l + k), a i) = ∑ j ∈ Finset.range k, a (l + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsingle : Finset.Ico (l + k) (l + (k + 1)) = {l + k} := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    calc
      _ = (∑ i ∈ Finset.Ico l (l + k), a i) +
          (∑ i ∈ Finset.Ico (l + k) (l + (k + 1)), a i) :=
        (join_intervals a (by omega) (by omega)).symm
      _ = _ := by rw [ih, hsingle, Finset.sum_singleton, Finset.sum_range_succ]

private theorem grows_by_shift {a : ℕ → ℕ} (ha : StrictMono a) (i k : ℕ) :
    a i + k ≤ a (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := ha (show i + k < i + (k + 1) by omega)
    omega

/-- When two successive block lengths are k and t ≥ k, the sum increases by at
least k². This remains true across an epoch boundary where the length grows. -/
theorem adjacent_block_gap {a : ℕ → ℕ} (ha : StrictMono a) (l k t : ℕ) (hkt : k ≤ t) :
    (∑ i ∈ Finset.Ico l (l + k), a i) + k ^ 2 ≤
      ∑ i ∈ Finset.Ico (l + k) (l + k + t), a i := by
  have hterm : (∑ j ∈ Finset.range k, (a (l + j) + k)) ≤
      ∑ j ∈ Finset.range k, a (l + k + j) := by
    apply Finset.sum_le_sum
    intro j _
    simpa only [Nat.add_right_comm l k j] using grows_by_shift ha (l + j) k
  have hprefix : (∑ i ∈ Finset.Ico l (l + k), a i) + k ^ 2 ≤
      ∑ i ∈ Finset.Ico (l + k) (l + k + k), a i := by
    rw [sum_shifted_range, sum_shifted_range]
    simpa [Finset.sum_add_distrib, pow_two] using hterm
  have hsplit := join_intervals a (show l + k ≤ l + k + k by omega)
    (show l + k + k ≤ l + k + t by omega)
  omega

end Erdos357Coarsen

open scoped BigOperators

namespace Erdos357Grouping

def block (a : ℕ → ℕ) (t k j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, a (t + j * k + i)

noncomputable def mass (a : ℕ → ℕ) (t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 : ℝ) / a (t + i)

private theorem mass_add (a : ℕ → ℕ) (t n m : ℕ) :
    mass a t (n + m) = mass a t n + mass a (t + n) m := by
  simp [mass, Finset.sum_range_add, Nat.add_assoc]

private theorem mass_succ (a : ℕ → ℕ) (t n : ℕ) :
    mass a t (n + 1) = mass a t n + 1 / a (t + n) := by
  simp [mass, Finset.sum_range_succ]

private theorem mass_mono (a : ℕ → ℕ) (t : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    mass a t n ≤ mass a t m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [mass_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)

private theorem block_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (t : ℕ) {k : ℕ} (hk : 0 < k) (j : ℕ) : 0 < block a t k j := by
  apply Finset.sum_pos (fun i _ => ha _)
  exact ⟨0, Finset.mem_range.mpr hk⟩

private theorem next_term_le (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hin : Monotone a)
    (t : ℕ) {k : ℕ} (hk : 0 < k) (j i : ℕ) :
    (1 : ℝ) / a (t + (j + 1) * k + i) ≤ k / block a t k j := by
  let z := a (t + (j + 1) * k + i)
  have hb : block a t k j ≤ k * z := by
    calc
      block a t k j ≤ ∑ _h ∈ Finset.range k, z := by
        apply Finset.sum_le_sum
        intro h hh
        have hlt := Finset.mem_range.mp hh
        apply hin
        rw [Nat.add_mul, Nat.one_mul]
        omega
      _ = k * z := by simp
  have hza : (0 : ℝ) < a (t + (j + 1) * k + i) := by exact_mod_cast ha _
  have hba : (0 : ℝ) < block a t k j := by exact_mod_cast block_pos a ha t hk j
  apply (div_le_div_iff₀ hza hba).mpr
  rw [one_mul]
  change ((block a t k j : ℕ) : ℝ) ≤ (k : ℝ) * (z : ℝ)
  exact_mod_cast hb

private theorem next_block_le (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hin : Monotone a)
    (t : ℕ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    mass a (t + (j + 1) * k) k ≤ (k : ℝ)^2 * (1 / block a t k j) := by
  calc
    mass a (t + (j + 1) * k) k ≤
        ∑ _i ∈ Finset.range k, (k : ℝ) / block a t k j :=
      Finset.sum_le_sum (fun i _ => next_term_le a ha hin t hk j i)
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv, pow_two, mul_assoc]

/-- Each original block after the first has reciprocal mass bounded by
    k² times the reciprocal of the previous block sum. -/
theorem grouped_comparison (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hin : Monotone a)
    (t : ℕ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    mass a (t + k) (n * k) ≤ (k : ℝ)^2 * mass (block a t k) 0 n := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    have hidx : t + k + n * k = t + (n + 1) * k := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [Nat.succ_mul, mass_add, mass_succ, Nat.zero_add, mul_add, hidx]
    exact add_le_add ih (next_block_le a ha hin t hk n)

/-- Starting at any cut t, some finite number of k-blocks carries any
    prescribed reciprocal mass. This is the finite witness needed for
    successive epochs with increasing group sizes. -/
theorem exists_epoch (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (hin : Monotone a)
    (hdiv : ¬ Summable (fun i => (1 : ℝ) / a i)) (t : ℕ) {k : ℕ}
    (hk : 0 < k) (target : ℝ) :
    ∃ n : ℕ, target ≤ mass (block a t k) 0 n := by
  by_contra! hbound
  apply hdiv
  apply summable_of_sum_range_le (c := mass a 0 (t + k) + (k : ℝ)^2 * target)
    (fun _ => by positivity)
  intro n
  have hnk : n ≤ n * k := by
    simpa using Nat.mul_le_mul_left n (show 1 ≤ k by omega)
  have hlen : n ≤ t + k + n * k := by omega
  change (∑ i ∈ Finset.range n, (1 : ℝ) / a i) ≤ _
  calc
    (∑ i ∈ Finset.range n, (1 : ℝ) / a i) = mass a 0 n := by simp [mass]
    _ ≤ mass a 0 (t + k + n * k) := mass_mono a 0 hlen
    _ = mass a 0 (t + k) + mass a (t + k) (n * k) := by rw [mass_add, Nat.zero_add]
    _ ≤ mass a 0 (t + k) + (k : ℝ)^2 * mass (block a t k) 0 n :=
      add_le_add le_rfl (grouped_comparison a ha hin t hk n)
    _ ≤ _ := by gcongr; exact (hbound n).le

end Erdos357Grouping

namespace Erdos357EpochAssembly

open Erdos357Grouping (block mass exists_epoch)
open Erdos357Coarsen (blockSum adjacent_block_gap sum_shifted_range)

private structure Plan (a : ℕ → ℕ) where
  count : ℕ → ℕ
  orig : ℕ → ℕ
  orig_zero : orig 0 = 0
  orig_succ : ∀ e, orig (e + 1) = orig e + count e * (e + 1)
  count_pos : ∀ e, 0 < count e
  unit_mass : ∀ e, 1 ≤ mass (block a (orig e) (e + 1)) 0 (count e)

private noncomputable def makePlan (a : ℕ → ℕ) (hp : ∀ n, 0 < a n)
    (hm : Monotone a) (hd : ¬ Summable (fun n => (1 : ℝ) / a n)) : Plan a := by
  classical
  have hex (e t : ℕ) : ∃ n : ℕ, (1 : ℝ) ≤ mass (block a t (e + 1)) 0 n :=
    exists_epoch a hp hm hd t (Nat.succ_pos e) 1
  let pick : ℕ → ℕ → ℕ := fun e t => (hex e t).choose
  have hmass (e t : ℕ) : 1 ≤ mass (block a t (e + 1)) 0 (pick e t) :=
    (hex e t).choose_spec
  let t : ℕ → ℕ := Nat.rec 0 (fun e start => start + pick e start * (e + 1))
  refine ⟨fun e => pick e (t e), t, rfl, fun _ => rfl, ?_, fun e => hmass e _⟩
  intro e
  by_contra! h
  have hz : pick e (t e) = 0 := by omega
  have hbad := hmass e (t e)
  norm_num [hz, mass] at hbad

variable {a : ℕ → ℕ} (p : Plan a)

private def start : ℕ → ℕ
  | 0 => 0
  | e + 1 => start e + p.count e

private theorem start_strict : StrictMono (start p) := by
  apply strictMono_nat_of_lt_succ
  intro e
  change start p e < start p e + p.count e
  have h := p.count_pos e
  omega

private theorem start_ge (e : ℕ) : e ≤ start p e := by
  induction e with
  | zero => exact Nat.zero_le _
  | succ e ih =>
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (start_strict p (Nat.lt_succ_self e)))

private theorem covers (j : ℕ) : ∃ e, j < start p (e + 1) := by
  exact ⟨j, lt_of_lt_of_le (Nat.lt_succ_self j) (start_ge p (j + 1))⟩

private noncomputable def epoch (j : ℕ) : ℕ := Nat.find (covers p j)

private theorem epoch_hi (j : ℕ) : j < start p (epoch p j + 1) :=
  Nat.find_spec (covers p j)

private theorem epoch_lo (j : ℕ) : start p (epoch p j) ≤ j := by
  cases he : epoch p j with
  | zero => exact Nat.zero_le _
  | succ e =>
    have hlt : e < Nat.find (covers p j) := by
      change e < epoch p j
      omega
    exact Nat.le_of_not_gt (Nat.find_min (covers p j) hlt)

private theorem epoch_eq {e j : ℕ} (hl : start p e ≤ j) (hu : j < start p (e + 1)) :
    epoch p j = e := by
  have hle : epoch p j ≤ e := Nat.find_min' (covers p j) hu
  by_contra h
  have hsc : epoch p j + 1 ≤ e := by omega
  have hbound := (start_strict p).monotone hsc
  have hj := epoch_hi p j
  omega

private theorem epoch_mono : Monotone (epoch p) := by
  intro i j hij
  exact Nat.find_min' (covers p i) (lt_of_le_of_lt hij (epoch_hi p j))

private theorem epoch_start (e : ℕ) : epoch p (start p e) = e :=
  epoch_eq p le_rfl (start_strict p (Nat.lt_succ_self e))

private noncomputable def cut (j : ℕ) : ℕ :=
  p.orig (epoch p j) + (j - start p (epoch p j)) * (epoch p j + 1)

private theorem cut_start (e : ℕ) : cut p (start p e) = p.orig e := by
  simp [cut, epoch_start]

private theorem cut_at (e j : ℕ) (hj : j ≤ p.count e) :
    cut p (start p e + j) = p.orig e + j * (e + 1) := by
  rcases lt_or_eq_of_le hj with h | rfl
  · have he : epoch p (start p e + j) = e := by
      apply epoch_eq p (Nat.le_add_right _ _)
      change start p e + j < start p e + p.count e
      omega
    simp [cut, he]
  · change cut p (start p (e + 1)) = _
    rw [cut_start, p.orig_succ]

private theorem cut_succ (i : ℕ) : cut p (i + 1) = cut p i + (epoch p i + 1) := by
  let e := epoch p i
  let j := i - start p e
  have hlo : start p e ≤ i := epoch_lo p i
  have hhi : i < start p e + p.count e := epoch_hi p i
  have hi : start p e + j = i := by dsimp [j]; omega
  have hj : j < p.count e := by omega
  have hc := cut_at p e j (by omega)
  have hn := cut_at p e (j + 1) (by omega)
  rw [hi] at hc
  rw [← Nat.add_assoc, hi, Nat.add_mul, Nat.one_mul] at hn
  change cut p (i + 1) = cut p i + (e + 1)
  omega

private theorem cut_strict : StrictMono (cut p) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [cut_succ]
  omega

private theorem block_at (e j : ℕ) (hj : j < p.count e) :
    blockSum a (cut p) (start p e + j) = block a (p.orig e) (e + 1) j := by
  have hu := cut_at p e (j + 1) (by omega)
  rw [← Nat.add_assoc, Nat.add_mul, Nat.one_mul] at hu
  unfold blockSum
  rw [cut_at p e j hj.le, hu, ← Nat.add_assoc, sum_shifted_range]
  rfl

private theorem partial_mass (e : ℕ) : (e : ℝ) ≤
    ∑ i ∈ Finset.range (start p e), (1 : ℝ) / blockSum a (cut p) i := by
  induction e with
  | zero => simp [start]
  | succ e ih =>
    have hm : (1 : ℝ) ≤ ∑ j ∈ Finset.range (p.count e),
        (1 : ℝ) / blockSum a (cut p) (start p e + j) := by
      calc
        (1 : ℝ) ≤ mass (block a (p.orig e) (e + 1)) 0 (p.count e) := p.unit_mass e
        _ = _ := by
          unfold mass
          apply Finset.sum_congr rfl
          intro j hj
          rw [Nat.zero_add, block_at p e j (Finset.mem_range.mp hj)]
    simp only [start, Finset.sum_range_add, Nat.cast_succ]
    exact add_le_add ih hm

private theorem no_sum : ¬ Summable (fun i => (1 : ℝ) / blockSum a (cut p) i) := by
  intro hs
  let total : ℝ := ∑' i, (1 : ℝ) / blockSum a (cut p) i
  obtain ⟨e, he⟩ := exists_nat_gt total
  have hbound : (∑ i ∈ Finset.range (start p e), (1 : ℝ) / blockSum a (cut p) i) ≤ total :=
    hs.sum_le_tsum _ (fun _ _ => by positivity)
  exact (not_le_of_gt he) ((partial_mass p e).trans hbound)

private theorem gap_bound (ha : StrictMono a) (i : ℕ) :
    blockSum a (cut p) i + (epoch p i + 1)^2 ≤ blockSum a (cut p) (i + 1) := by
  have hw : epoch p i + 1 ≤ epoch p (i + 1) + 1 :=
    Nat.add_le_add_right (epoch_mono p (Nat.le_succ i)) 1
  have h := adjacent_block_gap ha (cut p i) _ _ hw
  unfold blockSum
  rw [cut_succ p (i + 1), cut_succ p i]
  exact h

private theorem gap_top (ha : StrictMono a) :
    Filter.Tendsto (fun i => blockSum a (cut p) (i + 1) - blockSum a (cut p) i)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  apply Filter.eventually_atTop.2
  refine ⟨start p M, ?_⟩
  intro i hi
  have he := epoch_mono p hi
  rw [epoch_start] at he
  let w := epoch p i + 1
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hs : w ≤ w^2 := by
    simpa [pow_two] using Nat.mul_le_mul_left w hw
  have hg : blockSum a (cut p) i + w^2 ≤ blockSum a (cut p) (i + 1) := gap_bound p ha i
  change M ≤ blockSum a (cut p) (i + 1) - blockSum a (cut p) i
  have hm : M ≤ w := by dsimp [w]; omega
  omega

private theorem analytic_step : OMA.R_Erdos357_erdos_357_variants_infinite_set_sum_R1.H1 := by
  intro a hm hp hd
  let pl := makePlan a hp hm.monotone hd
  refine ⟨cut pl, cut_strict pl, ?_, ?_, no_sum pl⟩
  · apply strictMono_nat_of_lt_succ
    intro i
    have h := gap_bound pl hm i
    have hpos : 0 < (epoch pl i + 1)^2 := by positivity
    change blockSum a (cut pl) i < blockSum a (cut pl) (i + 1)
    omega
  · intro d
    exact Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 (gap_top pl hm) d)

end Erdos357EpochAssembly

theorem OMA.solution : OMA.R_Erdos357_erdos_357_variants_infinite_set_sum_R1.H1 :=
  Erdos357EpochAssembly.analytic_step

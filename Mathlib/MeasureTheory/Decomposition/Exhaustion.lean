/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Typeclasses

/-!
# Method of exhaustion

For `p : Set α → Prop` with `hp_empty : p ∅` and a finite measure `μ` on `α`, we construct
a measurable set `μ.maximalSet p hp_empty` which has maximal `μ`-measure among all measurable sets
with property `p`.
That is, `μ (μ.maximalSet p hp_empty) = ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s`.

That set is built as a supremum of a sequence of sets indexed by `ℕ`, with measure converging
to the supremum.

## Main definitions

* `MeasureTheory.Measure.maximalSet`: a measurable set which has maximal `μ`-measure among
  all measurable sets that satisfy a property `p : Set α → Prop`.

## Main statements

* `measurableSet_maximalSet`: `maximalSet` is a measurable set.
* `prop_maximalSet`: `maximalSet` satisfies the property `p` used to define it.
* `measure_maximalSet`: the measure of `maximalSet` is equal to the supremum of the measure of
  the measurable sets that satisfy `p`.
* `not_prop_of_subset_compl_maximalSet` : if a subset `s` of the complement of `maximalSet` has
  non-zero measure, it does not have property `p`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {p : Set α → Prop} {s : Set α}

/-- Let `p : Set α → Prop` be a predicate on sets and let `C` be the supremum of `μ s` over
all measurable sets `s` with property `p s`. `C` is finite since `μ` is a finite measure.
Then there exists a measurable set `t` with `p t` such that `μ t ≥ C - 1/n`. -/
lemma exists_set_measure_ge (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s) (n : ℕ) :
    ∃ t, MeasurableSet t ∧ p t
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s) - 1/n ≤ μ t := by
  by_cases hC_lt : 1/n < ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s ≤ μ Set.univ).trans_lt
        (measure_lt_top _ _)
      refine iSup_le (fun s ↦ ?_)
      exact iSup_le (fun _ ↦ iSup_le (fun _ ↦ measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne (ne_zero_of_lt hC_lt) (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s) - 1/n
        < ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s)
    have ht_meas : MeasurableSet t := by
      by_contra h_not_mem
      simp [h_not_mem] at ht
    have ht_mem : p t := by
      by_contra h_not_mem
      simp [h_not_mem] at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · obtain ⟨s, hs, hps⟩ := hp_exists
    refine ⟨s, hs, hps, ?_⟩
    rw [tsub_eq_zero_of_le (not_lt.mp hC_lt)]
    exact zero_le'

/-- A measurable set such that `p (μ.pSetGE μ n)` and for `C` the supremum of `μ s` over
all measurable sets `s` with `p s`, `μ (μ.pSetGE μ n) ≥ C - 1/n`. -/
def Measure.pSetGE (μ : Measure α) [IsFiniteMeasure μ] (p : Set α → Prop)
    (hp_exists : ∃ s, MeasurableSet s ∧ p s) (n : ℕ) : Set α :=
  (exists_set_measure_ge μ p hp_exists n).choose

lemma measurableSet_pSetGE (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s) (n : ℕ) :
    MeasurableSet (μ.pSetGE p hp_exists n) :=
  (exists_set_measure_ge μ p hp_exists n).choose_spec.1

lemma prop_pSetGE (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s) (n : ℕ) :
    p (μ.pSetGE p hp_exists n) :=
  (exists_set_measure_ge μ p hp_exists n).choose_spec.2.1

lemma measure_pSetGE_le (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s) (n : ℕ) :
    μ (μ.pSetGE p hp_exists n) ≤ ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s := by
  refine (le_iSup (f := fun s ↦ _) (prop_pSetGE μ p hp_exists n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p s), μ s) (μ.pSetGE p hp_exists n)
    (measurableSet_pSetGE p hp_exists n)

lemma measure_pSetGE_ge (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s) (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s) - 1/n ≤ μ (μ.pSetGE p hp_exists n) :=
  (exists_set_measure_ge μ p hp_exists n).choose_spec.2.2

lemma tendsto_measure_pSetGE (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s) :
    Tendsto (fun n ↦ μ (μ.pSetGE p hp_exists n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_pSetGE_ge μ p hp_exists) (measure_pSetGE_le μ p hp_exists)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

open Classical in
/-- A measurable set such that `p (μ.maximalSet p hp_empty)` and the measure
`μ (μ.maximalSet p hp_empty)` is maximal among such sets. -/
def Measure.maximalSet (μ : Measure α) [IsFiniteMeasure μ] (p : Set α → Prop) :
    Set α :=
  if hp_exists : ∃ s, MeasurableSet s ∧ p s then ⋃ n, μ.pSetGE p hp_exists n else ∅

lemma maximalSet_of_exists (hp_exists : ∃ s, MeasurableSet s ∧ p s) :
    μ.maximalSet p = ⋃ n, μ.pSetGE p hp_exists n :=
  dif_pos hp_exists

lemma maximalSet_of_not_exists (hp_empty : ¬ ∃ s, MeasurableSet s ∧ p s) :
    μ.maximalSet p = ∅ := dif_neg hp_empty

lemma measurableSet_maximalSet (p : Set α → Prop) :
    MeasurableSet (μ.maximalSet p) := by
  by_cases hp_exists : ∃ s, MeasurableSet s ∧ p s
  · rw [maximalSet_of_exists hp_exists]
    exact MeasurableSet.iUnion (measurableSet_pSetGE p hp_exists)
  · rw [maximalSet_of_not_exists hp_exists]
    exact .empty

lemma prop_maximalSet (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_exists : ∃ s, MeasurableSet s ∧ p s)
    (hp_iUnion : ∀ (t : ℕ → Set α) (_ : ∀ n, MeasurableSet (t n)) (_ : ∀ n, p (t n)),
      p (⋃ n, t n)) :
    p (μ.maximalSet p) := by
  rw [maximalSet_of_exists hp_exists]
  exact hp_iUnion _ (measurableSet_pSetGE p hp_exists) (prop_pSetGE μ p hp_exists)

/-- `μ.maximalSet p hp_empty` has maximal `μ`-measure among all measurable sets `s` with `p s`. -/
lemma measure_maximalSet (μ : Measure α) [IsFiniteMeasure μ] (p : Set α → Prop)
    (hp_iUnion : ∀ (t : ℕ → Set α) (_ : ∀ n, MeasurableSet (t n)) (_ : ∀ n, p (t n)),
      p (⋃ n, t n)) :
    μ (μ.maximalSet p) = ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s := by
  by_cases hp_exists : ∃ s, MeasurableSet s ∧ p s
  swap
  · rw [maximalSet_of_not_exists hp_exists, measure_empty]
    symm
    simp only [ENNReal.iSup_eq_zero]
    push_neg at hp_exists
    intro s hs hps
    exact absurd hps (hp_exists s hs)
  simp_rw [maximalSet_of_exists hp_exists]
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (prop_maximalSet μ p hp_exists hp_iUnion)).trans ?_
    convert le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p s), μ s) (μ.maximalSet p)
      (measurableSet_maximalSet p)
    rw [maximalSet_of_exists hp_exists]
  · exact le_of_tendsto' (tendsto_measure_pSetGE μ p hp_exists)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

lemma not_prop_of_subset_compl_maximalSet (μ : Measure α) [IsFiniteMeasure μ] (p : Set α → Prop)
    (hp_iUnion : ∀ (t : ℕ → Set α) (_ : ∀ n, MeasurableSet (t n)) (_ : ∀ n, p (t n)),
      p (⋃ n, t n))
    (hs : MeasurableSet s) (hs_subset : s ⊆ (μ.maximalSet p)ᶜ) (hμs : μ s ≠ 0) :
    ¬ p s := by
  by_cases hp_exists : ∃ s, MeasurableSet s ∧ p s
  swap
  · push_neg at hp_exists
    exact hp_exists s hs
  intro hsp
  have h_lt : μ (μ.maximalSet p) < μ (μ.maximalSet p ∪ s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right (measure_ne_top _ _) hμs
    · exact disjoint_compl_right.mono_right hs_subset
  have hp_union {s t} (hs : MeasurableSet s) (ht : MeasurableSet t) (hps : p s) (hpt : p t) :
      p (s ∪ t) := by
    let ts : ℕ → Set α := fun n ↦ if n = 0 then s else t
    have : s ∪ t = ⋃ n, ts n := by
      simp only [ts, Set.iUnion_ite, Set.iUnion_iUnion_eq_left]
      congr with x
      simp only [Set.mem_iUnion, exists_prop, exists_and_right, iff_and_self]
      exact fun _ ↦ ⟨1, by simp⟩
    rw [this]
    refine hp_iUnion ts (fun n ↦ ?_) (fun n ↦ ?_)
    · cases n with
      | zero => simp only [↓reduceIte, ts, hs]
      | succ n =>
          simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, ts, ht]
    · cases n with
      | zero => simp only [↓reduceIte, ts, hps]
      | succ n =>
          simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, ts, hpt]
  have h_le : μ (μ.maximalSet p ∪ s) ≤ μ (μ.maximalSet p) := by
    conv_rhs => rw [measure_maximalSet _ _ hp_iUnion]
    refine (le_iSup
      (f := fun (_ : p (μ.maximalSet p ∪ s)) ↦ _) ?_).trans ?_
    · exact hp_union (measurableSet_maximalSet p) hs (prop_maximalSet μ p hp_exists hp_iUnion) hsp
    · exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p _), μ s)
        (μ.maximalSet p ∪ s) ((measurableSet_maximalSet p).union hs)
  exact h_lt.not_le h_le

end MeasureTheory

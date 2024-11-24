/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Method of exhaustion

If `μ, μ` are two measures with `μ` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `μ t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT μ` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT μ)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT μ)ᶜ`, either `μ t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `μ` is not s-finite), we define
  `μ.sigmaFiniteSetWRT μ = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `μ`, for all sets `s`
  in `(sigmaFiniteSetWRT μ μ)ᶜ`, if `μ s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ μ)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ μ` and `μ` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT μ)ᶜ = ∞ • μ.restrict (μ.sigmaFiniteSetWRT μ)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

open scoped ENNReal NNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {g : α → ℝ≥0∞}

lemma exists_seq_tendsto_iSup {α β : Type*} [CompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β]
    {S : Set α} (hS : S.Nonempty) {F : α → β} (hS' : BddAbove (F '' S)) :
    ∃ u : ℕ → α, Monotone (fun n ↦ F (u n)) ∧ Tendsto (fun n ↦ F (u n)) atTop (𝓝 (⨆ a ∈ S, F a))
      ∧ ∀ n, u n ∈ S := by
  have h_seq := exists_seq_tendsto_sSup (S := F '' S)
    (by simp only [Set.image_nonempty]; exact hS) hS'
  choose g hg_mono hg₂ f hpf hFf_eq using h_seq
  have : sSup (F '' S) = ⨆ a ∈ S, F a := sSup_image
  rw [this] at hg₂
  refine ⟨f, ?_, ?_, hpf⟩
  · simp_rw [hFf_eq]
    exact hg_mono
  · simp_rw [hFf_eq]
    exact hg₂

/-- Let `p : Set α → Prop` be a predicate on sets and let `C` be the supremum of `μ s` over
all measurable sets `s` with property `p s`. `C` is finite since `μ` is a finite measure.
Then there exists a measurable set `t` with `p t` such that `μ t ≥ C - 1/n`. -/
lemma exists_fun_lintegral_ge (p : (α → ℝ≥0∞) → Prop) (hp_exists : ∃ f, Measurable f ∧ p f)
    (F : (α → ℝ≥0∞) → ℝ≥0∞) :
    ∃ f : ℕ → α → ℝ≥0∞, (∀ n, Measurable (f n)) ∧ (∀ n, p (f n))
      ∧ Monotone (fun n ↦ F (f n))
      ∧ Tendsto (fun n ↦ F (f n)) atTop (𝓝 (⨆ (g) (_ : Measurable g) (_ : p g), F g)) := by
  obtain ⟨f, hf_mono, hf_tendsto, hf⟩ :=
    exists_seq_tendsto_iSup hp_exists (OrderTop.bddAbove _) (F := F)
  choose hf_meas hfp using hf
  change Tendsto (fun n ↦ F (f n)) atTop (𝓝 (⨆ a ∈ {x | Measurable x ∧ p x}, F a))
    at hf_tendsto
  simp only [Set.mem_setOf_eq, iSup_and] at hf_tendsto
  exact ⟨f, hf_meas, hfp, hf_mono, hf_tendsto⟩

/-- A measurable function such that `p (μ.maximalFun p hp_zero hC)` and the integral of that
function is maximal (see `lintegral_maximalFun`). -/
noncomputable
def maximalFun (p : (α → ℝ≥0∞) → Prop) (hp_exists : ∃ f, Measurable f ∧ p f)
    (F : (α → ℝ≥0∞) → ℝ≥0∞) :
    α → ℝ≥0∞ :=
  fun a ↦ ⨆ n, (exists_fun_lintegral_ge p hp_exists F).choose n a

lemma measurable_maximalFun (p : (α → ℝ≥0∞) → Prop) (hp_exists : ∃ f, Measurable f ∧ p f)
    (F : (α → ℝ≥0∞) → ℝ≥0∞) :
    Measurable (maximalFun p hp_exists F) :=
  Measurable.iSup (exists_fun_lintegral_ge p hp_exists F).choose_spec.1

lemma prop_maximalFun (p : (α → ℝ≥0∞) → Prop) (hp_exists : ∃ f, Measurable f ∧ p f)
    (F : (α → ℝ≥0∞) → ℝ≥0∞)
    (hp_iUnion : ∀ (g : ℕ → α → ℝ≥0∞) (_ : ∀ n, Measurable (g n)) (_ : ∀ n, p (g n)),
      p (fun a ↦ ⨆ n, g n a)) :
    p (maximalFun p hp_exists F) :=
  hp_iUnion _ (exists_fun_lintegral_ge p hp_exists F).choose_spec.1
    (exists_fun_lintegral_ge p hp_exists F).choose_spec.2.1

/-- `μ.maximalFun p p hp_zero hC` has maximal integral among all measurable functions with
property `p`. -/
lemma lintegral_maximalFun (p : (α → ℝ≥0∞) → Prop) (hp_exists : ∃ f, Measurable f ∧ p f)
    (F : (α → ℝ≥0∞) → ℝ≥0∞)
    (hp_iUnion : ∀ (g : ℕ → α → ℝ≥0∞) (_ : ∀ n, Measurable (g n)) (_ : ∀ n, p (g n)),
      p (fun a ↦ ⨆ n, g n a))
    (hF_mono : Monotone F) :
    F (maximalFun p hp_exists F) = ⨆ (g) (_ : Measurable g) (_ : p g), F g := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (prop_maximalFun p hp_exists F hp_iUnion)).trans ?_
    exact le_iSup₂ (f := fun g _ ↦ ⨆ (_ : p g), F g) (maximalFun p hp_exists F)
      (measurable_maximalFun p hp_exists F)
  · refine le_of_tendsto' (exists_fun_lintegral_ge p hp_exists F).choose_spec.2.2.2 fun n ↦ ?_
    refine hF_mono fun a ↦ ?_
    exact le_iSup (fun n ↦ (exists_fun_lintegral_ge p hp_exists F).choose n a) n

end MeasureTheory

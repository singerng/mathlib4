/-
Copyright (c) 2023 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Real.ENNReal
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Group.Arithmetic


/-!
# Amenable Monoid Actions

In this file, we define amenability of a monoid action.
A monoid action is amenable if it admits an invariant mean.
A mean is like a probability measure, demanding
only finite additivity instead of σ-additivity.

## Main Definitions

- `Mean`: defines means as finitely additive probability measures
- `InvariantMean`: defines when a mean is invariant under a monoid action
- `amenable`: A monoid action is amenable if there exists an invariant mean

## Implementation Notes

`Mean` was not implemented using MeasureTheory.ProbabilityMeasure
because measures are σ-additive (i.e. countably additive). In this
setting, this would be a too strong assumption, we only want to demand
finite additivity. Typically, the resulting measures will not be
σ-additive.

## Todo

* `MeasurableSMul' should be replaced by `MeasurableConstSMul'
  once the latter is defined

## References

See [bartholdi2017amenability] for definitions
and more information on amenable actions.

-/

universe u v
variable (G : Type u) (α : Type v) [MeasurableSpace α]

/--A mean is a function from the power set of α to ENNReal that
assigns the value 1 to the full set α, and
is finitely additive under disjoint unions -/
structure Mean where
  /-- function giving the measure of a measurable subset-/
  measureOf : Set α  → NNReal
  /-- Set.univ has measure 1  -/
  measureOf_univ : measureOf Set.univ = 1
  /-- measureOf is finitely additive -/
  fin_add (X Y : Set α) (hX : MeasurableSet X) (hY : MeasurableSet Y) :
    Disjoint X Y → measureOf (X ∪ Y) = measureOf X + measureOf Y

@[coe]
instance : CoeFun (Mean α) (λ _ => Set α → NNReal) where
  coe := Mean.measureOf


variable [Monoid G] [MulAction G α] [MeasurableSpace G] [MeasurableSMul G α]

instance MeanSMul : SMul G (Mean α) where
  smul g μ := {
    measureOf := λ S => μ ((λ (x : α) => g • x)⁻¹' S)
    measureOf_univ := by simp only [Set.preimage_univ, μ.measureOf_univ]
    fin_add := by
      intro X Y hX hY disjXY
      simp only [Set.preimage_union]
      apply μ.fin_add ((λ (x:α) => g•x)⁻¹' X) ((λ (x:α) => g•x)⁻¹' Y) _ _ _
      apply measurable_const_smul; exact hX
      apply measurable_const_smul; exact hY
      apply Disjoint.preimage
      exact disjXY
  }

/--An invariant mean is a mean that is invariant
under translation with the monoid action-/
structure InvariantMean extends Mean α where
  /-- invariance of the mean -/
  invariance : ∀ (g : G), g • toMean = toMean


/-- A monoid action is amenable if there exists an invariant mean for it-/
class Amenable where
  invmean_nonempty := Nonempty (InvariantMean G α)

/-- For amenable actions, we can pick an invariant mean-/
noncomputable def invMean [Amenable G α] :
    InvariantMean G α :=
  by sorry

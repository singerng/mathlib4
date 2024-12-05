/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# C^-

-/

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category C]

def Minus [HasZeroMorphisms C] :=
  FullSubcategory (fun (K : CochainComplex C ℤ) => ∃ (n : ℤ), K.IsStrictlyLE n)

instance [HasZeroMorphisms C] : Category (Minus C) := by dsimp [Minus]; infer_instance

namespace Minus

section

variable [HasZeroMorphisms C]

def ι : Minus C ⥤ CochainComplex C ℤ := fullSubcategoryInclusion _

def fullyFaithfulι : (ι C).FullyFaithful :=
  fullyFaithfulFullSubcategoryInclusion _

instance : (ι C).Full := FullSubcategory.full _
instance : (ι C).Faithful := FullSubcategory.faithful _

variable {C} in
def quasiIso [CategoryWithHomology C] : MorphismProperty (Minus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

end

variable [Preadditive C]

noncomputable instance : HasShift (Minus C) ℤ :=
  (fullyFaithfulι C).hasShift
    (fun (n : ℤ) => FullSubcategory.lift _
    (Minus.ι C ⋙ CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) (by
      rintro ⟨K, k, hk⟩
      exact ⟨k - n, K.isStrictlyLE_shift k n _ (by omega)⟩))
    (fun n => FullSubcategory.lift_comp_inclusion _ _ _)

instance : (ι C).CommShift ℤ :=
  Functor.CommShift.of_hasShiftOfFullyFaithful _ _ _

end Minus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

def mapCochainComplexMinus : CochainComplex.Minus C ⥤ CochainComplex.Minus D :=
  FullSubcategory.lift _ (CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Minus.ι]
    infer_instance)

def mapCochainComplexMinusCompι :
    F.mapCochainComplexMinus ⋙ CochainComplex.Minus.ι D ≅
      CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory

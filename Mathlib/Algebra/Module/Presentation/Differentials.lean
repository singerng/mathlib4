/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.CotangentComplex
import Mathlib.RingTheory.Presentation

/-!
# Presentation of the module of differentials

Given a presentation of a `R`-algebra `S`, we obtain a presentation
of the `S`-module `Ω[S⁄R]`.

Assume `pres : Algebra.Presentation R S` is a presentation of `S` as an `R`-algebra.
We then have a type `pres.vars` for the generators, a type `pres.rels` for the relations,
and for each `r : pres.rels` we have the relation `pres.relation r` in `pres.Ring` (which is
a ring of polynomials over `R` with variables indexed by `pres.vars`).
Then, `Ω[pres.Ring⁄R]` identifies to the free module on the type `pres.vars`, and
for each `r : pres.rels`, we may consider the image of the differential of `pres.relation r`
in this free module, and by using the (surjective) map `pres.Ring → S`, we obtain
an element `pres.differentialsRelations.relation r` in the free `S`-module on `pres.vars`.
The main result in this file is that `Ω[S⁄R]` identifies to the quotient of the
free `S`-module on `pres.vars` by the submodule generated by these
elements `pres.differentialsRelations.relation r`. We show this as a consequence
of `Algebra.Extension.exact_cotangentComplex_toKaehler`
from the file `Mathlib.RingTheory.Kaehler.CotangentComplex`.

-/

universe w' t w u v

namespace Algebra.Presentation

open KaehlerDifferential

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation.{t, w} R S)

/-- The shape of the presentation by generators and relations of the `S`-module `Ω[S⁄R]`
that is obtained from a presentation of `S` as an `R`-algebra. -/
@[simps G R]
noncomputable def differentialsRelations : Module.Relations S where
  G := pres.vars
  R := pres.rels
  relation r :=
    Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
      ((mvPolynomialBasis R pres.vars).repr (D _ _ (pres.relation r)))

namespace differentials

/-! We obtain here a few compatibilities which allow to compare the two sequences
`(pres.rels →₀ S) → (pres.vars →₀ S) → Ω[S⁄R]` and
`pres.toExtension.Cotangent →ₗ[S] pres.toExtension.CotangentSpace → Ω[S⁄R]`.
Indeed, there is commutative diagram with a surjective map
`hom₁ : (pres.rels →₀ S) →ₗ[S] pres.toExtension.Cotangent` on the left and
bijections on the middle and on the right. Then, the exactness of the first
sequence shall follow from the exactness of the second which is
`Algebra.Extension.exact_cotangentComplex_toKaehler`. -/

/-- Same as `comm₂₃` below, but here we have not yet constructed `differentialsSolution`. -/
lemma comm₂₃' : pres.toExtension.toKaehler.comp pres.cotangentSpaceBasis.repr.symm.toLinearMap =
    Finsupp.linearCombination S (fun g ↦ D _ _ (pres.val g)) := by
  ext g
  dsimp
  rw [Basis.repr_symm_apply, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, one_smul, one_smul,
    Generators.cotangentSpaceBasis_apply, mapBaseChange_tmul, one_smul]
  simp

/-- The canonical map `(pres.rels →₀ S) →ₗ[S] pres.toExtension.Cotangent`. -/
noncomputable def hom₁ : (pres.rels →₀ S) →ₗ[S] pres.toExtension.Cotangent :=
  Finsupp.linearCombination S (fun r ↦ Extension.Cotangent.mk ⟨pres.relation r, by simp⟩)

lemma hom₁_single (r : pres.rels) :
    hom₁ pres (Finsupp.single r 1) = Extension.Cotangent.mk ⟨pres.relation r, by simp⟩ := by
  simp [hom₁]

lemma surjective_hom₁ : Function.Surjective (hom₁ pres) := by
  let φ : (pres.rels →₀ S) →ₗ[pres.Ring] pres.toExtension.Cotangent :=
    { toFun := hom₁ pres
      map_add' := by simp
      map_smul' := by simp }
  change Function.Surjective φ
  have h₁ := Algebra.Extension.Cotangent.mk_surjective (P := pres.toExtension)
  have h₂ : Submodule.span pres.Ring
      (Set.range (fun r ↦ (⟨pres.relation r, by simp⟩ : pres.ker))) = ⊤ := by
    refine Submodule.map_injective_of_injective (f := Submodule.subtype pres.ker)
      Subtype.coe_injective ?_
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span,
      Submodule.coe_subtype, Ideal.submodule_span_eq]
    simp only [← pres.span_range_relation_eq_ker]
    congr
    aesop
  rw [← LinearMap.range_eq_top] at h₁ ⊢
  rw [← top_le_iff, ← h₁, LinearMap.range_eq_map, ← h₂]
  dsimp
  rw [Submodule.map_span_le]
  rintro _ ⟨r, rfl⟩
  simp only [LinearMap.mem_range]
  refine ⟨Finsupp.single r 1, ?_⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, hom₁_single, φ]
  rfl

lemma comm₁₂_single (r : pres.rels) :
    pres.toExtension.cotangentComplex (hom₁ pres (Finsupp.single r 1)) =
      pres.cotangentSpaceBasis.repr.symm ((differentialsRelations pres).relation r) := by
  simp only [hom₁, Finsupp.linearCombination_single, one_smul, differentialsRelations,
    Basis.repr_symm_apply, Extension.cotangentComplex_mk]
  exact pres.cotangentSpaceBasis.repr.injective (by ext; simp)

lemma comm₁₂ : pres.toExtension.cotangentComplex.comp (hom₁ pres) =
    pres.cotangentSpaceBasis.repr.symm.comp (differentialsRelations pres).map := by
  ext r
  have := (differentialsRelations pres).map_single
  dsimp at this ⊢
  rw [comm₁₂_single, this]

end differentials

open differentials in
/-- The `S`-module `Ω[S⁄R]` contains an obvious solution to the system of linear
equations `pres.differentialsRelations.Solution` when `pres` is a presentation
of `S` as an `R`-algebra. -/
noncomputable def differentialsSolution :
    pres.differentialsRelations.Solution (Ω[S⁄R]) where
  var g := D _ _ (pres.val g)
  linearCombination_var_relation r := by
    simp only [differentialsRelations_G, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, ← comm₂₃', ← comm₁₂_single]
    apply DFunLike.congr_fun (Function.Exact.linearMap_comp_eq_zero
      (pres.toExtension.exact_cotangentComplex_toKaehler))

lemma differentials.comm₂₃ :
    pres.toExtension.toKaehler.comp pres.cotangentSpaceBasis.repr.symm.toLinearMap =
      pres.differentialsSolution.π :=
  comm₂₃' pres

open differentials in
lemma differentialsSolution_isPresentation :
    pres.differentialsSolution.IsPresentation := by
  rw [Module.Relations.Solution.isPresentation_iff]
  constructor
  · rw [← Module.Relations.Solution.surjective_π_iff_span_eq_top, ← comm₂₃]
    exact Extension.toKaehler_surjective.comp pres.cotangentSpaceBasis.repr.symm.surjective
  · rw [← Module.Relations.range_map]
    exact Function.Exact.linearMap_ker_eq
      ((LinearMap.exact_iff_of_surjective_of_bijective_of_injective
      _ _ _ _ (hom₁ pres)
      pres.cotangentSpaceBasis.repr.symm.toLinearMap .id
      (comm₁₂ pres) (by simpa using comm₂₃ pres) (surjective_hom₁ pres)
        (LinearEquiv.bijective _) (Equiv.refl _).injective).2
        pres.toExtension.exact_cotangentComplex_toKaehler)

/-- The presentation of the `S`-module `Ω[S⁄R]` deduced from a presentation
of `S` as a `R`-algebra. -/
noncomputable def differentials : Module.Presentation S (Ω[S⁄R]) where
  toSolution := differentialsSolution pres
  toIsPresentation := pres.differentialsSolution_isPresentation

end Algebra.Presentation

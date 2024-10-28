/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Quotient

/-!
# Presentations of modules

Given a ring `A`, we introduce a structure `Relations A` which
contains the data that is necessary to define a module by generators and relations.
A term `relations : Relations A` involves two index types: a type `G` for the
generators and a type `R` for the relations. The relation attached to `r : R` is
an element `G →₀ A` which expresses the coefficients of the expected linear relation.

One may think of `relations : Relations A` as a particular shape for systems of
linear equations in any `A`-module `M`. Each `g : G` can be thought of as a
variable (in `M`) and each `r : R` specifies a linear relation that these
variables should satisfy. This way, we get a type `relations.Solution M`.
Then, if `solution : relations.Solution M`, we introduce the predicate
`solution.IsPresentation` which asserts that `solution` is the universal
solution to the given equations, i.e. `solution` gives a presentation
of `M` by generators and relations.

Given an `A`-module `M`, we also introduce the type `Presentation A M` which
contains all the data and properties involved in a presentation of `M` by
generators and relations.

## TODO
* Relate this to `Module.FinitePresentation`
* Behaviour of presentations with respect to the extension of scalars and
the restriction of scalars

-/

universe w' w'' w₀ w₁ v'' v' v u

namespace Module

variable (A : Type u) [Ring A]

/-- Given a ring `A`, this structure involves a family of elements (indexed by a type `R`)
in a free module `G →₀ A`. This allows to define an `A`-module by generators and relations,
see `Relations.Quotient`. -/
@[nolint checkUnivs]
structure Relations where
  /-- the index type for generators -/
  G : Type w₀
  /-- the index type for relations -/
  R : Type w₁
  /-- the coefficients of the linear relations that are expected between the generators -/
  relation (r : R) : G →₀ A

namespace Relations

variable {A} (relations : Relations.{w₀, w₁} A)

/-- The module that is presented by generators and relations given by `relations : Relations A`.
This is the quotient of the free `A`-module on `relations.G` by the submodule generated by
the given relations. -/
abbrev Quotient := (relations.G →₀ A) ⧸ Submodule.span A (Set.range relations.relation)

/-- The canonical (surjective) linear map `(relations.G →₀ A) →ₗ[A] relations.Quotient`. -/
def toQuotient : (relations.G →₀ A) →ₗ[A] relations.Quotient := Submodule.mkQ _

lemma surjective_toQuotient : Function.Surjective relations.toQuotient :=
  Submodule.mkQ_surjective _

lemma ker_toQuotient :
    LinearMap.ker relations.toQuotient = Submodule.span A (Set.range relations.relation) :=
  Submodule.ker_mkQ _

@[simp]
lemma toQuotient_relation (r : relations.R) :
    relations.toQuotient (relations.relation r) = 0 := by
  dsimp only [toQuotient]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (by simp)

/-- The linear map `(relations.R →₀ A) →ₗ[A] (relations.G →₀ A)` corresponding to the relations
given by `relations : Relations A`. -/
noncomputable def map : (relations.R →₀ A) →ₗ[A] (relations.G →₀ A) :=
  Finsupp.linearCombination _ relations.relation

@[simp]
lemma map_single (r : relations.R) :
    relations.map (Finsupp.single r 1) = relations.relation r := by
  simp [map]

@[simp]
lemma range_map :
    LinearMap.range relations.map = Submodule.span A (Set.range relations.relation) :=
  Finsupp.range_linearCombination _

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- The type of solutions in a module `M` of the equations given by `relations : Relations A`. -/
@[ext]
structure Solution where
  /-- the image in `M` of each variable -/
  var (g : relations.G) : M
  linearCombination_var_relation (r : relations.R) :
    Finsupp.linearCombination _ var (relations.relation r) = 0

namespace Solution

variable {relations M}

section

variable (solution : relations.Solution M)

/-- Given `relations : Relations A` and a solution in `relations.Solution M`, this is
the linear map `(relations.G →₀ A) →ₗ[A] M` canonically associated to the . -/
noncomputable def π : (relations.G →₀ A) →ₗ[A] M := Finsupp.linearCombination _ solution.var

@[simp]
lemma π_single (g : relations.G) :
    solution.π (Finsupp.single g 1) = solution.var g := by simp [π]

@[simp]
lemma π_relation (r : relations.R) : solution.π (relations.relation r) = 0 :=
  solution.linearCombination_var_relation r

@[simp]
lemma π_comp_map : solution.π.comp relations.map = 0 := by aesop

@[simp]
lemma π_comp_map_apply (x : relations.R →₀ A) : solution.π (relations.map x) = 0 := by
  change solution.π.comp relations.map x = 0
  rw [π_comp_map, LinearMap.zero_apply]

/-- Given `relations : Relations A` and `solution : relations.Solution M`,
this is the canonical linear map from `relations.R →₀ A` to the kernel
of `solution.π : (relations.G →₀ A) →ₗ[A] M`. -/
noncomputable def mapToKer : (relations.R →₀ A) →ₗ[A] (LinearMap.ker solution.π) :=
  LinearMap.codRestrict _ relations.map (by simp)

@[simp]
lemma mapToKer_coe (x : relations.R →₀ A) : (solution.mapToKer x).1 = relations.map x := rfl

lemma span_relation_le_ker_π :
    Submodule.span A (Set.range relations.relation) ≤ LinearMap.ker solution.π := by
  rw [Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, π_relation]

/-- Given `relations : Relations A` and `solution : relations.Solution M`, this is
the canonical linear map `relations.Quotient →ₗ[A] M` from the module. -/
noncomputable def fromQuotient : relations.Quotient →ₗ[A] M :=
  Submodule.liftQ _ solution.π solution.span_relation_le_ker_π

@[simp]
lemma fromQuotient_mk (x : relations.G →₀ A) :
    solution.fromQuotient (Submodule.Quotient.mk x) = solution.π x := rfl

@[simp]
lemma fromQuotient_comp_toQuotient :
    solution.fromQuotient.comp relations.toQuotient = solution.π := rfl

@[simp]
lemma fromQuotient_toQuotient (x : relations.G →₀ A) :
    solution.fromQuotient (relations.toQuotient x) = solution.π x := rfl

variable {N : Type v'} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N)

/-- The image of a solution to `relations : Relation A` by a linear map `M →ₗ[A] N`. -/
@[simps]
def postcomp : relations.Solution N where
  var g := f (solution.var g)
  linearCombination_var_relation r := by
    have : Finsupp.linearCombination _ (fun g ↦ f (solution.var g)) = f.comp solution.π := by aesop
    simp [this]

@[simp]
lemma postcomp_comp {N' : Type v''} [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') :
    solution.postcomp (g.comp f) = (solution.postcomp f).postcomp g := rfl

@[simp]
lemma postcomp_id : solution.postcomp LinearMap.id = solution := rfl

variable {solution}

lemma congr_var {solution' : relations.Solution M} (h : solution = solution') (g : relations.G) :
    solution.var g = solution'.var g := by rw [h]

lemma congr_postcomp {solution' : relations.Solution M} (h : solution = solution')
    (f : M →ₗ[A] N) : solution.postcomp f = solution'.postcomp f := by rw [h]

end

section

variable (π : (relations.G →₀ A) →ₗ[A] M) (hπ : ∀ (r : relations.R), π (relations.relation r) = 0)

/-- Given `relations : Relations A` and an `A`-module `M`, this is a constructor
for `relations.Solution M` for which the data is given as
a linear map `π : (relations.G →₀ A) →ₗ[A] M`. (See also `ofπ'` for an alternate
vanishing criterion.) -/
@[simps (config := .lemmasOnly)]
noncomputable def ofπ : relations.Solution M where
  var g := π (Finsupp.single g 1)
  linearCombination_var_relation r := by
    have : π = Finsupp.linearCombination _ (fun g ↦ π (Finsupp.single g 1)) := by ext; simp
    rw [← this]
    exact hπ r

@[simp]
lemma ofπ_π : (ofπ π hπ).π = π := by ext; simp [ofπ]

end

section

variable (π : (relations.G →₀ A) →ₗ[A] M) (hπ : π.comp relations.map = 0)

/-- Variant of `ofπ` where the vanishing condition is expressed in terms
of a composition of linear maps. -/
@[simps! (config := .lemmasOnly)]
noncomputable def ofπ' : relations.Solution M :=
  ofπ π (fun r ↦ by
    simpa using DFunLike.congr_fun hπ (Finsupp.single r 1))

@[simp]
lemma ofπ'_π : (ofπ' π hπ).π = π := by simp [ofπ']

end

/-- Given `relations : Relations A`, an `A`-module `M` and `solution : relations.Solution M`,
this property asserts that `solution` gives a presentation of `M` by generators and relations. -/
structure IsPresentation (solution : relations.Solution M) : Prop where
  bijective : Function.Bijective solution.fromQuotient

namespace IsPresentation

variable {solution : relations.Solution M} (h : solution.IsPresentation)

include h

/-- When `M` admits a presentation by generators and relations given
by `solution : relations.Solutions M`, this is the associated linear equivalence
`relations.Quotient ≃ₗ[A] M`. -/
noncomputable def linearEquiv : relations.Quotient ≃ₗ[A] M := LinearEquiv.ofBijective _ h.bijective

@[simp]
lemma linearEquiv_apply (x : relations.Quotient) :
    h.linearEquiv x = solution.fromQuotient x := rfl

@[simp]
lemma linearEquiv_symm_var (g : relations.G) :
    h.linearEquiv.symm (solution.var g) = Submodule.Quotient.mk (Finsupp.single g 1) :=
  h.linearEquiv.injective (by simp)

lemma surjective_π : Function.Surjective solution.π := by
  rw [← fromQuotient_comp_toQuotient, LinearMap.coe_comp]
  exact h.bijective.2.comp relations.surjective_toQuotient

lemma ker_π : LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  rw [← ker_toQuotient, ← fromQuotient_comp_toQuotient, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.2 h.bijective.1, Submodule.comap_bot]

lemma surjective_mapToKer : Function.Surjective solution.mapToKer := by
  rintro ⟨x, hx⟩
  rw [h.ker_π, ← relations.range_map] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

/-- The sequence `(relations.R →₀ A) → (relations.G →₀ A) → M → 0` is exact. -/
lemma exact : Function.Exact relations.map solution.π := by
  intro x₂
  constructor
  · intro hx₂
    obtain ⟨x₁, hx₁⟩ := h.surjective_mapToKer ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [mapToKer_coe, Subtype.ext_iff] using hx₁⟩
  · rintro ⟨x₁, rfl⟩
    rw [π_comp_map_apply]

variable {N : Type v'} [AddCommGroup N] [Module A N]

/-- If `M` admits a presentation by generators and relations, and we have a solution of the
same equations in a module `N`, then this is the canonical induced linear map `M →ₗ[A] N`. -/
noncomputable def desc (s : relations.Solution N) : M →ₗ[A] N :=
  s.fromQuotient.comp h.linearEquiv.symm.toLinearMap

@[simp]
lemma desc_var (s : relations.Solution N) (g : relations.G) :
    h.desc s (solution.var g) = s.var g := by
  dsimp [desc]
  rw [linearEquiv_symm_var, fromQuotient_mk, π_single]

@[simp]
lemma desc_comp_π (s : relations.Solution N) : (h.desc s).comp solution.π = s.π := by aesop

@[simp]
lemma π_desc_apply (s : relations.Solution N) (x : relations.G →₀ A) :
    h.desc s (solution.π x) = s.π x :=
  DFunLike.congr_fun (h.desc_comp_π s) x

@[simp]
lemma postcomp_desc (s : relations.Solution N) :
    solution.postcomp (h.desc s) = s := by aesop

lemma postcomp_injective {f f' : M →ₗ[A] N}
    (h' : solution.postcomp f = solution.postcomp f') : f = f' := by
  suffices f.comp solution.fromQuotient = f'.comp solution.fromQuotient by
    ext x
    obtain ⟨y, rfl⟩ := h.bijective.2 x
    exact DFunLike.congr_fun this y
  ext g
  simpa using congr_var h' g

/-- If `M` admits a presentation by generators and relations, then
linear maps from `M` can be (naturally) identified to the solutions of
certain linear equations. -/
@[simps]
noncomputable def linearMapEquiv : (M →ₗ[A] N) ≃ relations.Solution N where
  toFun f := solution.postcomp f
  invFun s := h.desc s
  left_inv f := h.postcomp_injective (by aesop)
  right_inv s := by aesop

section

variable {solution' : relations.Solution N} (h' : solution'.IsPresentation)

/-- Uniqueness (up to a unique linear equivalence) of the module defined
by generators and relations. -/
noncomputable def uniq : M ≃ₗ[A] N := LinearEquiv.ofLinear
  (h.desc solution') (h'.desc solution)
    (h'.postcomp_injective (by simp))
    (h.postcomp_injective (by simp))

@[simp]
lemma postcomp_uniq : solution.postcomp (uniq h h').toLinearMap = solution' := by
  simp [uniq]

@[simp]
lemma postcomp_uniq_symm : solution'.postcomp (uniq h h').symm.toLinearMap = solution := by
  simp [uniq]

@[simp]
lemma uniq_var (g : relations.G) : uniq h h' (solution.var g) = solution'.var g := by
  simp [uniq]

@[simp]
lemma uniq_symm_var (g : relations.G) : (uniq h h').symm (solution'.var g) = solution.var g := by
  simp [uniq]

end

lemma ofLinearEquiv (e : M ≃ₗ[A] N) : (solution.postcomp e.toLinearMap).IsPresentation where
  bijective := by
    have : (solution.postcomp e.toLinearMap).fromQuotient =
      e.toLinearMap.comp (solution.fromQuotient) := by aesop
    rw [this, LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact Function.Bijective.comp e.bijective h.bijective

end IsPresentation

variable (relations)

/-- Given `relations : Relations A`, this is the obvious solution to `relations`
in the quotient `relations.Quotient`. -/
@[simps!]
noncomputable def ofQuotient : relations.Solution relations.Quotient :=
  ofπ relations.toQuotient (by simp)

@[simp]
lemma ofQuotient_π : (ofQuotient relations).π = Submodule.mkQ _ := ofπ_π _ _

@[simp]
lemma ofQuotient_fromQuotient : (ofQuotient relations).fromQuotient = .id := by aesop

lemma ofQuotient_isPresentation : (ofQuotient relations).IsPresentation where
  bijective := by
    simpa only [ofQuotient_fromQuotient, LinearMap.id_coe] using Function.bijective_id

variable {relations}

/-- Helper structure in order to prover `Module.Relations.Solutions.IsPresentation`
by showing the universal property of the module defined by generators and relations.
The universal property is restricted to modules that are in `Type w'` for
an auxiliary universes `w'`. See `IsPresentationCore.isPresentation`. -/
structure IsPresentationCore (solution : relations.Solution M) where
  /-- any solution in a module `N : Type w'` is obtained in a unique way
  by postcomposing `solution : relations.Solution M` by a linear map `M →ₗ[A] N`. -/
  desc {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) : M →ₗ[A] N
  postcomp_desc {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) :
    solution.postcomp (desc s) = s
  postcomp_injective {N : Type w'} [AddCommGroup N] [Module A N] {f f' : M →ₗ[A] N}
      (h : solution.postcomp f = solution.postcomp f') : f = f'

namespace IsPresentationCore

variable {solution : relations.Solution M}

@[simp]
lemma desc_var (h : IsPresentationCore.{w'} solution)
    {N : Type w'} [AddCommGroup N] [Module A N] (s : relations.Solution N) (g : relations.G) :
    h.desc s (solution.var g) = s.var g :=
  congr_var (h.postcomp_desc s) g

/-- The structure `IsPresentationCore` can be shrunk to a lower universe. -/
def down (h : IsPresentationCore.{max w' w''} solution) :
    IsPresentationCore.{w''} solution where
  desc s := ULift.moduleEquiv.toLinearMap.comp
    (h.desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
  postcomp_desc s:= by
    simpa using congr_postcomp
      (h.postcomp_desc (s.postcomp ULift.moduleEquiv.symm.toLinearMap))
        ULift.moduleEquiv.toLinearMap
  postcomp_injective {N _ _ f f'} h' := by
    ext x
    have := congr_postcomp h' ULift.moduleEquiv.{_, _, w'}.symm.toLinearMap
    simp only [← postcomp_comp] at this
    simpa using DFunLike.congr_fun (h.postcomp_injective this) x

lemma isPresentation {solution : relations.Solution M}
    (h : IsPresentationCore.{max u v w₀} solution) :
    solution.IsPresentation where
  bijective := by
    let e : relations.Quotient ≃ₗ[A] M :=
      LinearEquiv.ofLinear solution.fromQuotient
      ((down.{v} h).desc (ofQuotient relations))
      ((down.{max u w₀} h).postcomp_injective (by aesop)) (by aesop)
    exact e.bijective

end IsPresentationCore

end Solution

end Relations

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- Given an `A`-module `M`, a term in this type is a presentation by `M` by
generators and relations. -/
@[nolint checkUnivs]
structure Presentation extends Relations.{w₀, w₁} A,
  toRelations.Solution M, toSolution.IsPresentation where

variable {A M}

/-- Constructor for `Module.Presentation`. -/
@[simps toRelations toSolution]
def Presentation.ofIsPresentation {relations : Relations.{w₀, w₁} A}
    {solution : relations.Solution M} (h : solution.IsPresentation) :
    Presentation.{w₀, w₁} A M where
  toSolution := solution
  toIsPresentation := h

end Module

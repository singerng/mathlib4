/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Presentation of a direct sum

If `M : ι → Type _` is a family of `A`-modules, then the data of a presentation
of each `M i`, we obtain a presentation of the module `⨁ i, M i`.

-/

universe w' w₀ w₁ w v u

namespace Module

open DirectSum

variable {A : Type u} [Ring A] {ι : Type w} [DecidableEq ι]
  (relations : ι → Relations.{w₀, w₁} A)
  {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

namespace Relations

/-- The direct sum operations on `Relations A`. Given a family
`relations : ι → Relations A`, the type of generators and relations
in `directSum relations` are the corresponding `Sigma` types. -/
@[simps G R relation]
noncomputable def directSum : Relations A where
  G := Σ i, (relations i).G
  R := Σ i, (relations i).R
  relation := fun ⟨i, r⟩ ↦ Finsupp.embDomain (Function.Embedding.sigmaMk
      (β := fun i ↦ (relations i).G) i) ((relations i).relation r)

namespace Solution

variable {relations}
variable {N : Type v} [AddCommGroup N] [Module A N]

/-- Given an `A`-module `N` and a family `relations : ι → Relations A`,
the data of a solution of `Relations.directSum relations` in `N`
is equivalent to the data of a family of solutions of `relations i` in `N`
for all `i`. -/
@[simps]
def directSumEquiv :
    (Relations.directSum relations).Solution N ≃
      ∀ i, (relations i).Solution N where
  toFun s i :=
    { var := fun g ↦ s.var ⟨i, g⟩
      linearCombination_var_relation := fun r ↦ by
        rw [← s.linearCombination_var_relation ⟨i, r⟩]
        symm
        apply Finsupp.linearCombination_embDomain }
  invFun t :=
    { var := fun ⟨i, g⟩ ↦ (t i).var g
      linearCombination_var_relation := fun ⟨i, r⟩ ↦ by
        erw [← (t i).linearCombination_var_relation r]
        apply Finsupp.linearCombination_embDomain }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Given `solution : ∀ (i : ι), (relations i).Solution (M i)`, this is the
canonical solution of `Relations.directSum relations` in `⨁ i, M i`. -/
@[simps! var]
def directSum (solution : ∀ (i : ι), (relations i).Solution (M i)) :
    (Relations.directSum relations).Solution (⨁ i, M i) :=
  directSumEquiv.symm (fun i ↦ (solution i).postcomp (lof A ι M i))

namespace IsPresentation

variable {solution : ∀ (i : ι), (relations i).Solution (M i)}
  (h : ∀ i, (solution i).IsPresentation)

/-- The direct sum admits a presentation by generators and relations. -/
noncomputable def directSum.isRepresentationCore :
    Solution.IsPresentationCore.{w'} (directSum solution) where
  desc s := DirectSum.toModule _ _ _ (fun i ↦ (h i).desc (directSumEquiv s i))
  postcomp_desc s := by ext ⟨i, g⟩; simp
  postcomp_injective {N _ _ f f'} h' := by
    ext i : 1
    apply (h i).postcomp_injective
    ext g
    exact Solution.congr_var h' ⟨i, g⟩

include h in
lemma directSum : (directSum solution).IsPresentation :=
  (directSum.isRepresentationCore h).isPresentation

end IsPresentation

end Solution

end Relations

namespace Presentation

/-- The obvious presentation of the module `⨁ i, M i` that is obtained from
the data of presentations of the module `M i` for each `i`. -/
@[simps! G R relation var]
noncomputable def directSum (pres : ∀ (i : ι), Presentation A (M i)) :
    Presentation A (⨁ i, M i) :=
  ofIsPresentation
    (Relations.Solution.IsPresentation.directSum (fun i ↦ (pres i).toIsPresentation))

/-- The obvious presentation of the module `ι →₀ M` that is deduced from a presentation
of the module `M`. -/
noncomputable def finsupp {M : Type v} [AddCommGroup M] [Module A M]
    (pres : Presentation A M) (ι : Type w)
    [DecidableEq ι] [DecidableEq M] : Presentation A (ι →₀ M) :=
  (directSum (fun (i : ι) ↦ pres)).ofLinearEquiv (by
    symm
    apply finsuppAddEquivDFinsupp.toLinearEquiv
    intros
    sorry)

end Presentation

end Module

/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal closed structure on `Module R`.
-/

suppress_compilation

universe v w x u

open CategoryTheory Opposite

namespace ModuleCat

variable {R : Type u} [CommRing R]

-- Not sure how to define these, presumably there's some abstract machine that does exactly this!
def asHom₂ {M N P : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) :
    M ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op N)).obj P := sorry

-- Not sure how to define these, presumably there's some abstract machine that does exactly this!
def Hom.hom₂ {M N P : ModuleCat.{u} R}
    (f : ModuleCat.Hom M (((linearCoyoneda R (ModuleCat R)).obj (op N)).obj P)) :
    M →ₗ[R] N →ₗ[R] P := sorry

/-- Auxiliary definition for the `MonoidalClosed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking. )
-/
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
  toFun f := asHom₂ <| LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ asHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    intro m n
    rw [hom_comp, LinearMap.comp_apply]
    -- This used to be `rw` and was longer (?), but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.braiding_hom_apply, TensorProduct.lift.tmul]
  right_inv _ := rfl

instance : MonoidalClosed (ModuleCat.{u} R) where
  closed M :=
    { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              -- Porting note: this proof was automatic in mathlib3
              homEquiv_naturality_left_symm := by
                intros
                apply TensorProduct.ext'
                intro m n
                rfl } }

theorem ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N)) :
    (ihom M).map f g = g ≫ f :=
  rfl

open MonoidalCategory

-- Porting note: `CoeFun` was replaced by `DFunLike`
-- I can't seem to express the function coercion here without writing `@DFunLike.coe`.
theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    ((MonoidalClosed.curry f).hom y).hom x = f (x ⊗ₜ[R] y) :=
  rfl

@[simp]
theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) = (f y).hom x :=
  rfl

/-- Describes the counit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this
should give a map `M ⊗ Hom(M, N) ⟶ N`, so we flip the order of the arguments in the identity map
`Hom(M, N) ⟶ (M ⟶ N)` and uncurry the resulting map `M ⟶ Hom(M, N) ⟶ N.` -/
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = ModuleCat.asHom₂ (TensorProduct.uncurry _ _ _ _ LinearMap.id.flip) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry

/-- Describes the unit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this should
define a map `N ⟶ Hom(M, M ⊗ N)`, which is given by flipping the arguments in the natural
`R`-bilinear map `M ⟶ N ⟶ M ⊗ N`. -/
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = ModuleCat.asHom₂ (TensorProduct.mk _ _ _).flip :=
  rfl

theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = ModuleCat.asHom₂ (LinearMap.lcomp R _ f) :=
  rfl

end ModuleCat

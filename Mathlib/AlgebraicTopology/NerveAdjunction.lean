/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/

import Mathlib.AlgebraicTopology.HomotopyCat
import Mathlib.AlgebraicTopology.Nerve
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Category.ReflQuiv
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Combinatorics.Quiver.ReflQuiver

namespace CategoryTheory

open Category Functor Limits Opposite SimplexCategory Simplicial SSet
universe v u

section

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

private def ι0₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1
private def ι1₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2
private def ι2₂ : [0]₂ ⟶ [2]₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

private def ev0₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι0₂.op φ
private def ev1₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι1₂.op φ
private def ev2₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : OneTruncation₂ V := V.map ι2₂.op φ

private def δ1₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 1
private def δ2₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 2
private def δ0₂ : [1]₂ ⟶ [2]₂ := δ₂ (n := 1) 0

private def ev02₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, opstuff V rfl, opstuff V rfl⟩
private def ev01₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ, opstuff V (SimplexCategory.δ_comp_δ (j := 1) le_rfl), opstuff V rfl⟩
private def ev12₂ {V : SSet.Truncated 2} (φ : V _[2]₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    opstuff V (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm,
    opstuff V rfl⟩

@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def forgetToReflQuiv.natIso : nerveFunctor₂ ⋙ SSet.oneTruncation₂.{u} ≅ ReflQuiv.forget :=
  OneTruncation₂.nerve₂.natIso ≪≫ OneTruncation.ofNerve.natIso

@[simps!]
def nerve₂Adj.counit.component (C : Cat.{u, u}) :
    SSet.hoFunctor₂.obj (nerveFunctor₂.obj C) ⥤ C := by
  fapply Quotient.lift
  · exact (whiskerRight (forgetToReflQuiv.natIso).hom _ ≫ ReflQuiv.adj.{u}.counit).app C
  · intro x y f g rel
    cases rel; rename_i φ
    simp [ReflQuiv.adj, Quot.liftOn, Cat.FreeRefl.quotientFunctor, Quotient.functor,
      Quiv.adj, Quiv.id_eq_id]
    change OneTruncation.ofNerve.map (ev02₂ φ) =
      OneTruncation.ofNerve.map (ev01₂ φ) ≫ OneTruncation.ofNerve.map (ev12₂ φ)
    simp [OneTruncation.ofNerve.map]
    exact φ.map_comp (X := (0 : Fin 3)) (Y := 1) (Z := 2)
      (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.component_eq (C : Cat) :
    SSet.hoFunctor₂Obj.quotientFunctor (nerve₂ C) ⋙ nerve₂Adj.counit.component.{u} C =
    (whiskerRight forgetToReflQuiv.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app C := rfl

theorem nerve₂Adj.counit.naturality' ⦃C D : Cat.{u, u}⦄ (F : C ⟶ D) :
    (nerveFunctor₂ ⋙ SSet.hoFunctor₂).map F ⋙ nerve₂Adj.counit.component D =
      nerve₂Adj.counit.component C ⋙ F := by
  apply SSet.hoFunctor₂Obj.lift_unique'
  have := SSet.hoFunctor₂_naturality (nerveFunctor₂.map F)
  conv =>
    lhs; rw [← Functor.assoc]; lhs; apply this.symm
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, Functor.comp_map]
  rw [← Functor.assoc _ _ F]
  conv => rhs; lhs; exact (nerve₂Adj.counit.component_eq C)
  conv =>
    rhs
    exact ((whiskerRight forgetToReflQuiv.natIso.hom Cat.freeRefl ≫
      ReflQuiv.adj.counit).naturality F).symm
  simp only [component, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app, comp_obj,
    ReflQuiv.forget_obj, id_obj, whiskerRight_app, Cat.comp_eq_comp, Functor.comp_map,
    Functor.assoc, hoFunctor₂Obj.quotientFunctor, Cat.freeRefl_obj_α, ReflQuiv.of_val]
  rw [Quotient.lift_spec]

def nerve₂Adj.counit : nerveFunctor₂ ⋙ SSet.hoFunctor₂.{u} ⟶ (𝟭 Cat) where
  app := nerve₂Adj.counit.component
  naturality := nerve₂Adj.counit.naturality'

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

def toNerve₂.mk.app {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (n : SimplexCategory.Truncated 2) :
    X.obj (op n) ⟶ (nerveFunctor₂.obj C).obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => .mk₀ (F.obj x)
  | 1 => exact fun f => .mk₁ (F.map ⟨f, rfl, rfl⟩)
  | 2 => exact fun φ => .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (x : X _[0]₂) :
    mk.app F [0]₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (f : X _[1]₂) :
    mk.app F [1]₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (φ : X _[2]₂) :
    mk.app F [2]₂ φ = .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ)) := rfl

/-- This is similiar to one of the famous Segal maps, except valued in a product rather than a
pullback.-/
noncomputable def nerve₂.seagull (C : Cat.{v, u}) :
    (nerveFunctor₂.obj C).obj (op [2]₂) ⟶
    (nerveFunctor₂.obj C).obj (op [1]₂) ⨯ (nerveFunctor₂.obj C).obj (op [1]₂) :=
  prod.lift ((nerveFunctor₂.obj C).map (.op δ2₂)) ((nerveFunctor₂.obj C).map (.op δ0₂))

instance (C : Cat) : Mono (nerve₂.seagull C) where
  right_cancellation {X} (f g : X → ComposableArrows C 2) eq := by
    ext x
    simp [nerve₂.seagull] at eq
    have eq1 := congr($eq ≫ prod.fst)
    have eq2 := congr($eq ≫ prod.snd)
    simp at eq1 eq2
    replace eq1 := congr_fun eq1 x
    replace eq2 := congr_fun eq2 x
    simp at eq1 eq2
    generalize f x = fx at *
    generalize g x = gx at *
    clear eq x f g
    fapply ComposableArrows.ext₂
    · exact congrArg (·.obj 0) <| eq1
    · exact congrArg (·.obj 1) <| eq1
    · exact congrArg (·.obj 1) <| eq2
    · have := congr_arg_heq (·.hom) <| eq1
      refine (conj_eqToHom_iff_heq' _ _ _ _).2 this
    · have := congr_arg_heq (·.hom) <| eq2
      refine (conj_eqToHom_iff_heq' _ _ _ _).2 this

@[simps!] def toNerve₂.mk {X : SSet.Truncated.{u} 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C where
      app := fun n => toNerve₂.mk.app F n.unop
      naturality := by
        rintro ⟨⟨m, hm⟩⟩ ⟨⟨n, hn⟩⟩ ⟨α : (⟨n, hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨m, hm⟩⟩
        rw [show Opposite.op α = α.op by rfl]
        induction' m using SimplexCategory.rec with m
        induction' n using SimplexCategory.rec with n
        dsimp at α ⊢
        let OK {n m hn hm} (f : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩) :=
          X.map f.op ≫ mk.app F ⟨[n], hn⟩ = mk.app F ⟨[m], hm⟩ ≫ (nerveFunctor₂.obj C).map f.op
        show OK α
        have fac : ∀ {n m hn hm} {α : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩} k hk
            {β : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[k], hk⟩}
            {γ : (⟨[k], hk⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩},
            α = β ≫ γ → OK β → OK γ → OK α := by
          rintro _ _ _ _ _ k hk β γ rfl h1 h2
          dsimp only [OK] at h1 h2 ⊢
          rw [op_comp, map_comp, map_comp, assoc, h1, ← assoc, h2, assoc]
        have const10 (α : [1]₂ ⟶ [0]₂) : OK α := by
          ext x
          cases SimplexCategory.eq_const_to_zero α
          dsimp
          fapply ComposableArrows.ext₁
          · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.src]
            congr 1
            refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
            rw [← map_comp, ← map_id]; congr 1
            apply Quiver.Hom.unop_inj
            apply SimplexCategory.hom_zero_zero
          · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.tgt]
            congr 1
            refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
            rw [← map_comp, ← map_id]; congr 1
            apply Quiver.Hom.unop_inj
            apply SimplexCategory.hom_zero_zero
          · refine eq_of_heq <|
              (?_ : HEq _ (ComposableArrows.mk₁ (C := C) (𝟙rq (F.obj x))).hom).trans ?_
            · have : ∀ x' a b (h : _ = a ∧ _ = b), x = a → x = b → x' = X.map (σ₂ (n := 0) 0).op x →
                HEq (ComposableArrows.mk₁ (C := C) (F.map ⟨x', h⟩)).hom
                  (ComposableArrows.mk₁ (C := C) (𝟙rq (F.obj x))).hom := by
                rintro _ _ _ _ rfl rfl rfl
                exact congr_arg_heq (fun a => (ComposableArrows.mk₁ (C := C) a).hom) (F.map_id x)
              apply this
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.src]
                refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
                rw [← map_comp, ← map_id]; congr 1
                apply Quiver.Hom.unop_inj
                apply SimplexCategory.hom_zero_zero
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.tgt]
                refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
                rw [← map_comp, ← map_id]; congr 1
                apply Quiver.Hom.unop_inj
                apply SimplexCategory.hom_zero_zero
              · rw [← eq_const_to_zero]
            · simp; rfl
        have const01 (α : [0]₂ ⟶ [1]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          simp only [ComposableArrows.obj', Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
            ComposableArrows.mk₀_obj, comp_obj, nerveFunctor_obj, whiskeringLeft_obj_obj,
            Functor.comp_map, op_obj, op_map, Quiver.Hom.unop_op', nerve_map, Quiver.Hom.unop_op,
            SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj, Monotone.functor_obj,
            ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
          obtain ⟨i : Fin 2, rfl⟩ := eq_const_of_zero' α
          match i with
          | 0 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [1] 0 = δ₂ 1))
            ext i; match i with | 0 => rfl
          | 1 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [1] 1 = δ₂ 0))
            ext i; match i with | 0 => rfl
        have const02 (α : [0]₂ ⟶ [2]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          obtain ⟨i : Fin 3, rfl⟩ := eq_const_of_zero' α
          match i with
          | 0 =>
            revert x; intro f
            refine congrArg F.obj (?_ : _ = X.map _ _)
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 0 = ι0₂))
            ext i; match i with | 0 => rfl
          | 1 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 1 = ι1₂))
            ext i; match i with | 0 => rfl
          | 2 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 2 = ι2₂))
            ext i; match i with | 0 => rfl
        have nat1m {m hm} (α : [1]₂ ⟶ ⟨[m], hm⟩) : OK α := by
          match m with
          | 0 => apply const10
          | 1 =>
            match α, eq_of_one_to_one α with
            | _, .inr rfl =>
              dsimp [OK]
              rw [(_ : X.map _ = id), (_ : Prefunctor.map _ _ = id)]; rfl
              all_goals apply map_id
            | _, .inl ⟨i, rfl⟩ =>
              exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const01 ..)
          | 2 =>
            match α, eq_of_one_to_two α with
            | _, .inl rfl =>
              ext x
              simp [SimplexCategory.rec]
              fapply ComposableArrows.ext₁
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.src]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.tgt]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp [ev12₂, ev01₂, nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨1, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp, ← op_comp]; congr 2
                  ext (i : Fin 1); match i with | 0 => rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inl rfl) =>
              ext x
              simp [SimplexCategory.rec]
              fapply ComposableArrows.ext₁
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.src]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.tgt]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp [ev12₂, ev01₂, nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                refine HEq.trans ?_ (heq_of_eq (hyp x))
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inr (.inl rfl)) =>
              ext x
              simp [SimplexCategory.rec]
              fapply ComposableArrows.ext₁
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.src]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp [nerveFunctor₂, SSet.truncation, OneTruncation₂.tgt]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp [ev12₂, ev01₂, nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨1, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp [δ0₂, δ0, δ₂, OneTruncation₂.src, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp, ← op_comp]; congr 2
                  ext (i : Fin 1); match i with | 0 => rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inr (.inr ⟨i, rfl⟩)) =>
              exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const02 ..)
        have nat2m (α : [2]₂ ⟶ ⟨[m], hm⟩) : OK α := by
          dsimp [OK]
          apply (cancel_mono (nerve₂.seagull _)).1
          simp [nerve₂.seagull]
          congr 1 <;> rw [← map_comp, ← op_comp, ← nat1m, ← nat1m, op_comp, map_comp, assoc]
        match n with
        | 0 =>
          match m with
          | 0 =>
            ext x
            simp [SimplexCategory.rec]
            apply ComposableArrows.ext₀
            simp only [ComposableArrows.obj', Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
              ComposableArrows.mk₀_obj, comp_obj, nerveFunctor_obj, whiskeringLeft_obj_obj,
              Functor.comp_map, op_obj, op_map, Quiver.Hom.unop_op', nerve_map, Quiver.Hom.unop_op,
              SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj, Monotone.functor_obj]
            cases SimplexCategory.hom_zero_zero α
            congr 1
            exact congr_fun (X.map_id _) x
          | 1 => apply const01
          | 2 => apply const02
        | 1 => apply nat1m
        | 2 => apply nat2m

/-- We might prefer this version where we are missing the analogue of the hypothesis hyp
conjugated by the isomorphism nerve₂Adj.NatIso.app C -/
@[simps!] def toNerve₂.mk' {X : SSet.Truncated.{u} 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev01₂ φ))
        ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C :=
  toNerve₂.mk (f ≫ (forgetToReflQuiv.natIso.app C).hom) hyp

theorem oneTruncation₂_toNerve₂Mk' {X : SSet.Truncated 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C) ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev01₂ φ))
        ((f ≫ (forgetToReflQuiv.natIso.app C).hom).map (ev12₂ φ))) :
    oneTruncation₂.map (toNerve₂.mk' f hyp) = f := by
  refine ReflPrefunctor.ext (fun _ ↦ ComposableArrows.ext₀ rfl)
    (fun X Y g ↦ eq_of_heq ((heq_eqRec_iff_heq _ _ _).2 <| (heq_eqRec_iff_heq _ _ _).2 ?_))
  simp [oneTruncation₂]
  have {A B A' B' : OneTruncation₂ (nerveFunctor₂.obj C)}
      : A = A' → B = B' → ∀ (x : A ⟶ B) (y : A' ⟶ B'), x.1 = y.1 → HEq x y := by
    rintro rfl rfl ⟨⟩ ⟨⟩ ⟨⟩; rfl
  apply this
  · exact ComposableArrows.ext₀ rfl
  · exact ComposableArrows.ext₀ rfl
  · simp
    fapply ComposableArrows.ext₁ <;> simp [ReflQuiv.comp_eq_comp]
    · rw [g.2.1]; exact congr_arg (·.obj 0) (f.map g).2.1.symm
    · rw [g.2.2]; exact congr_arg (·.obj 1) (f.map g).2.2.symm
    · refine (conj_eqToHom_iff_heq' _ _ _ _).2 ?_
      simp [ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map]
      obtain ⟨g, rfl, rfl⟩ := g
      rfl

/-- Now do a case split. For n = 0 and n = 1 this is covered by the hypothesis.
         For n = 2 this is covered by the new lemma above.-/
theorem toNerve₂.ext {X : SSet.Truncated 2} {C : Cat} (f g : X ⟶ nerve₂ C)
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  have eq₀ x : f.app (op [0]₂) x = g.app (op [0]₂) x := congr(($hyp).obj x)
  have eq₁ x : f.app (op [1]₂) x = g.app (op [1]₂) x := congr((($hyp).map ⟨x, rfl, rfl⟩).1)
  ext ⟨⟨n, hn⟩⟩ x
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => apply eq₀
  | 1 => apply eq₁
  | 2 =>
    apply Functor.hext (fun i : Fin 3 => ?_) (fun (i j : Fin 3) k => ?_)
    · let pt : [0]₂ ⟶ [2]₂ := SimplexCategory.const _ _ i
      refine congr(($(congr_fun (f.naturality pt.op) x)).obj 0).symm.trans ?_
      refine .trans ?_ congr(($(congr_fun (g.naturality pt.op) x)).obj 0)
      exact congr($(eq₀ _).obj 0)
    · let ar : [1]₂ ⟶ [2]₂ := mkOfLe _ _ k.le
      have h1 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (f.naturality (op ar)) x)
      have h2 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (g.naturality (op ar)) x)
      exact h1.symm.trans <| .trans (congr_arg_heq (fun x => x.map' 0 1) (eq₁ _)) h2

/-- ER: This is dumb. -/
theorem toNerve₂.ext' {X : SSet.Truncated 2} {C : Cat} (f g : X ⟶ nerveFunctor₂.obj C)
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  let f' : X ⟶ nerve₂ C := f
  let g' : X ⟶ nerve₂ C := g
  exact toNerve₂.ext f' g' hyp

-- @[simps! toPrefunctor obj map]
def nerve₂Adj.unit.component (X : SSet.Truncated.{u} 2) :
    X ⟶ nerveFunctor₂.obj (SSet.hoFunctor₂.obj X) := by
  fapply toNerve₂.mk' (C := SSet.hoFunctor₂.obj X)
  · exact (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    (forgetToReflQuiv.natIso).inv.app (SSet.hoFunctor₂.obj X))
  · exact fun φ ↦ Quotient.sound _ (HoRel₂.mk φ)

theorem nerve₂Adj.unit.component_eq (X : SSet.Truncated.{u} 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.component X) =
    ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor ⋙rq
    (forgetToReflQuiv.natIso).inv.app (SSet.hoFunctor₂.obj X) := by
  apply oneTruncation₂_toNerve₂Mk'

def nerve₂Adj.unit : 𝟭 (SSet.Truncated.{u} 2) ⟶ hoFunctor₂ ⋙ nerveFunctor₂ where
  app := nerve₂Adj.unit.component
  naturality := by
    refine fun V W f ↦ toNerve₂.ext' (f ≫ nerve₂Adj.unit.component W)
      (nerve₂Adj.unit.component V ≫ nerveFunctor₂.map (hoFunctor₂.map f)) ?_
    rw [Functor.map_comp, Functor.map_comp, nerve₂Adj.unit.component_eq,
      nerve₂Adj.unit.component_eq]
    have nat₁ := (forgetToReflQuiv.natIso).inv.naturality (hoFunctor₂.map f)
    repeat rw [← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)]
    repeat rw [assoc]
    simp at nat₁
    rw [← nat₁]
    rfl

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
nonrec def nerve₂Adj : SSet.hoFunctor₂.{u} ⊣ nerveFunctor₂ := by
  refine Adjunction.mkOfUnitCounit {
    unit := nerve₂Adj.unit
    counit := nerve₂Adj.counit
    left_triangle := ?_
    right_triangle := ?_
  }
  · ext X
    apply SSet.hoFunctor₂Obj.lift_unique'
    simp only [id_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, NatTrans.comp_app,
      whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    rw [← Cat.comp_eq_comp
      (SSet.hoFunctor₂Obj.quotientFunctor X) (𝟙 (SSet.hoFunctor₂.obj X))]
    rw [comp_id, Cat.comp_eq_comp, ← Functor.assoc]
    conv =>
      lhs; lhs; apply (SSet.hoFunctor₂_naturality (nerve₂Adj.unit.component X)).symm
    simp only [comp_obj, Cat.freeRefl_obj_α, Functor.comp_map]
    rw [nerve₂Adj.unit.component_eq X, Functor.assoc]
    conv =>
      lhs; rhs
      apply (nerve₂Adj.counit.component_eq (SSet.hoFunctor₂.obj X))
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc, NatTrans.comp_app, id_obj, whiskerRight_app]
    rw [← Cat.comp_eq_comp, ← assoc, ← Cat.freeRefl.map_comp, ReflQuiv.comp_eq_comp,
      ReflPrefunctor.comp_assoc]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp]
    simp only [ReflQuiv.forget_obj, comp_obj, Iso.inv_hom_id_app]
    rw [ReflQuiv.id_eq_id]
    simp_rw [ReflPrefunctor.comp_id
      (U := ReflQuiv.of _) (V := ReflQuiv.of ↑(SSet.hoFunctor₂.obj X))
      ((SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    rw [← ReflQuiv.comp_eq_comp (Z := ReflQuiv.of _)
      (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X))
      ((SSet.hoFunctor₂Obj.quotientFunctor X).toReflPrefunctor)]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, map_comp, assoc]
    have nat := ReflQuiv.adj.counit.naturality
      (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
      (Y := SSet.hoFunctor₂.obj X) (SSet.hoFunctor₂Obj.quotientFunctor X)
    dsimp at nat
    rw [nat, ← assoc]
    conv => lhs; lhs; apply ReflQuiv.adj.left_triangle_components (SSet.oneTruncation₂.obj X)
    simp
  · refine NatTrans.ext (funext fun C ↦ ?_)
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerLeft_app, associator_inv_app,
      whiskerRight_app, id_comp, NatTrans.id_app']
    apply toNerve₂.ext
    simp only [map_comp, map_id]
    rw [nerve₂Adj.unit, nerve₂Adj.unit.component_eq]
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp, ← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)
      (Z := ReflQuiv.of _), assoc, assoc, ← Functor.comp_map,
        ← forgetToReflQuiv.natIso.inv.naturality]
    conv => lhs; rhs; rw [← assoc] --
    show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
    rw [← ReflQuiv.forget.map_comp]
    show _ ≫ ReflQuiv.forget.map (SSet.hoFunctor₂Obj.quotientFunctor (nerve₂ ↑C)
      ⋙ nerve₂Adj.counit.app C) ≫ _ = _
    rw [nerve₂Adj.counit, nerve₂Adj.counit.component_eq]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app,
      comp_obj, id_obj, whiskerRight_app]
    rw [ReflQuiv.forget.map_comp, ← Functor.comp_map, ← assoc, ← assoc]
    have := ReflQuiv.adj.unit.naturality (forgetToReflQuiv.natIso.hom.app C)
    simp only [Functor.comp_obj] at this
    conv => lhs; lhs; lhs; apply this.symm
    simp only [Cat.freeRefl_obj_α, id_obj, Functor.id_map]
    slice_lhs 2 3 => rw [ReflQuiv.adj.right_triangle_components C]
    simp

instance nerveFunctor₂.faithful : nerveFunctor₂.{u, u}.Faithful := by
  haveI lem := ReflQuiv.forget.Faithful -- TODO: why is this needed
  exact Functor.Faithful.of_comp_iso
    (G := oneTruncation₂) (H := ReflQuiv.forget) forgetToReflQuiv.natIso

instance nerveFunctor₂.full : nerveFunctor₂.{u, u}.Full where
  map_surjective := by
    intro X Y F
    let uF := SSet.oneTruncation₂.map F
    let uF' : X ⥤rq Y :=
      forgetToReflQuiv.natIso.inv.app X ≫ uF ≫ forgetToReflQuiv.natIso.hom.app Y
    have {a b c : X} (h : a ⟶ b) (k : b ⟶ c) :
        uF'.map (h ≫ k) = uF'.map h ≫ uF'.map k := by
      let hk := ComposableArrows.mk₂ h k
      let Fh : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ h)
      let Fk : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ k)
      let Fhk' : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ (h ≫ k))
      let Fhk : ComposableArrows Y 2 := F.app (op [2]₂) hk
      have lem0 := congr_fun (F.naturality δ0₂.op) hk
      have lem1 := congr_fun (F.naturality δ1₂.op) hk
      have lem2 := congr_fun (F.naturality δ2₂.op) hk
      replace lem0 := congr_arg_heq (·.map' 0 1) lem0
      replace lem1 := congr_arg_heq (·.map' 0 1) lem1
      replace lem2 := congr_arg_heq (·.map' 0 1) lem2
      have eq0 : (nerveFunctor₂.obj X).map δ0₂.op hk = .mk₁ k := by
        apply ComposableArrows.ext₁ rfl rfl
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
      have eq2 : (nerveFunctor₂.obj X).map δ2₂.op hk = .mk₁ h := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      have eq1 : (nerveFunctor₂.obj X).map δ1₂.op hk = .mk₁ (h ≫ k) := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      simp at lem0 lem1 lem2
      rw [eq0] at lem0
      rw [eq1] at lem1
      rw [eq2] at lem2
      replace lem0 : HEq (uF'.map k) (Fhk.map' 1 2) := by
        refine HEq.trans (b := Fk.map' 0 1) ?_ lem0
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF]
        rfl
      replace lem2 : HEq (uF'.map h) (Fhk.map' 0 1) := by
        refine HEq.trans (b := Fh.map' 0 1) ?_ lem2
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF]
        rfl
      replace lem1 : HEq (uF'.map (h ≫ k)) (Fhk.map' 0 2) := by
        refine HEq.trans (b := Fhk'.map' 0 1) ?_ lem1
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF]
        rfl
      rw [Fhk.map'_comp 0 1 2] at lem1
      refine eq_of_heq (lem1.trans (heq_comp ?_ ?_ ?_ lem2.symm lem0.symm))
      · simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι0₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
      · simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι1₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
      · simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation.ofNerve.map, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι2₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
    let fF : X ⥤ Y := ReflPrefunctor.toFunctor uF' this
    have eq : fF.toReflPrefunctor = uF' := rfl
    refine ⟨fF, toNerve₂.ext' (nerveFunctor₂.map fF) F ?_⟩
    · have nat := forgetToReflQuiv.natIso.hom.naturality fF
      simp at nat
      rw [eq] at nat
      simp [uF', uF] at nat
      exact (Iso.cancel_iso_hom_right (oneTruncation₂.map (nerveFunctor₂.map fF))
        (oneTruncation₂.map F) (forgetToReflQuiv.natIso.app Y)).mp nat

noncomputable instance nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor₂

instance nerve₂Adj.reflective : Reflective nerveFunctor₂.{u, u} :=
  Reflective.mk SSet.hoFunctor₂ nerve₂Adj

end

noncomputable def nerveAdjunction : SSet.hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp nerve₂Adj) Nerve.cosk2Iso.symm

/-- Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently.-/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful := by
  have := SSet.coskeleton.faithful 2
  exact Functor.Faithful.of_iso (F := (nerveFunctor₂.{u, u} ⋙ ran (Δ.ι 2).op)) Nerve.cosk2Iso.symm

instance nerveFunctor.full : nerveFunctor.{u, u}.Full := by
  have := SSet.coskeleton.full 2
  exact Functor.Full.of_iso (F := (nerveFunctor₂.{u, u} ⋙ ran (Δ.ι 2).op)) Nerve.cosk2Iso.symm

noncomputable instance nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor

instance nerveCounit_isIso : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

noncomputable def nerveCounitNatIso : nerveFunctor ⋙ SSet.hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)

noncomputable instance : Reflective nerveFunctor where
  L := SSet.hoFunctor
  adj := nerveAdjunction

end CategoryTheory

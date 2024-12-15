/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.CharacterModule

/-!
This file shows that the functors `Grp.uliftFunctor` and `CommGrp.uliftFunctor`
(as well as the additive versions) are fully faithful, preserves all limits and
create small limits.

It also shows that `AddCommGrp.uliftFunctor` preserves zero morphisms and is an additive functor.

-/

universe v w w' u

open CategoryTheory Limits

namespace Grp

/-- The universe lift functor for groups is faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

/-- The universe lift functor for groups is full.
-/
@[to_additive
  "The universe lift functor for additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ Grp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
      preserves {c} lc := by
        apply ReflectsLimit.reflects (F := forget Grp.{max u v})
        set e : CategoryTheory.uliftFunctor.{v,u}.mapCone ((forget Grp).mapCone c) ≅
            (forget Grp).mapCone (uliftFunctor.mapCone c) := Cones.ext (Iso.refl _) (fun _ ↦ rfl)
        exact IsLimit.ofIsoLimit (Classical.choice (PreservesLimit.preserves
          (F := CategoryTheory.uliftFunctor) (Classical.choice (PreservesLimit.preserves
          (F := forget Grp) lc)))) e

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where
      preservesLimit := inferInstance

/--
The universe lift for groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
      preservesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance uliftFunctor_preservesLimits :
    PreservesLimits uliftFunctor.{v, u} := uliftFunctor_preservesLimitsOfSize

/--
The universe lift functor on `Grp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddGrp.{u}` creates `u`-small limits."
]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end Grp

namespace CommGrp

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  "The universe lift functor for commutative additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  "The universe lift functor for commutative additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ CommGrp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
      preserves {c} lc := by
        apply ReflectsLimit.reflects (F := forget CommGrp.{max u v})
        set e : CategoryTheory.uliftFunctor.{v,u}.mapCone ((forget CommGrp).mapCone c) ≅
            (forget CommGrp).mapCone (uliftFunctor.mapCone c) :=
          Cones.ext (Iso.refl _) (fun _ ↦ rfl)
        exact IsLimit.ofIsoLimit (Classical.choice (PreservesLimit.preserves
          (F := CategoryTheory.uliftFunctor) (Classical.choice (PreservesLimit.preserves
          (F := forget CommGrp) lc)))) e

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where
      preservesLimit := inferInstance

/--
The universe lift for commutative groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for commutative additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
      preservesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance uliftFunctor_preservesLimits :
    PreservesLimits uliftFunctor.{v, u} := uliftFunctor_preservesLimitsOfSize

/--
The universe lift functor on `CommGrp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddCommGrp.{u}` creates `u`-small limits."
]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end CommGrp

namespace AddCommGroup

/-- The universe lift for commutative additive groups preserves zero morphisms.
-/
instance uliftFunctor_preservesZeroMorphisms :
    AddCommGrp.uliftFunctor.{u,v}.PreservesZeroMorphisms := {map_zero := fun X Y ↦ by rfl}

instance uliftFunctor_additive :
    AddCommGrp.uliftFunctor.{u,v}.Additive where map_add := rfl

end AddCommGroup

namespace AddCommGrp

variable {J : Type w} [Category.{w'} J] {K : J ⥤ AddCommGrp.{u}} {c : Cocone K}
  {lc : Cocone (K ⋙ AddCommGrp.uliftFunctor.{v,u})} (hc : IsColimit c)

variable {A A' : Type} [AddCommGroup A] [AddCommGroup A']

def coconeOfChar (f : lc.pt →+ A) : Cocone K where
  pt := AddCommGrp.of (ULift A)
  ι :=
  { app j := AddCommGrp.ofHom (((@AddEquiv.ulift A _).symm.toAddMonoidHom.comp f).comp
             ((lc.ι.app j).comp (@AddEquiv.ulift (K.obj j) _).symm.toAddMonoidHom))
    naturality {j j'} u := by
      ext a
      have := lc.ι.naturality u
      apply_fun (fun f ↦ f {down := a}) at this
      simp
      change lc.ι.app j' {down := K.map u a} = _ at this
      change ({down := f (lc.ι.app j' {down := K.map u a})} : ULift A) = _
      rw [this]; rfl
  }

def descChar (f : lc.pt →+ A) : c.pt →+ A :=
  AddEquiv.ulift.toAddMonoidHom.comp (hc.desc (coconeOfChar f))

lemma descChar_fac (f : lc.pt →+ A) (j : J) (a : K.obj j) :
    (descChar hc f) (c.ι.app j a) = f ((lc.ι.app j {down := a})) := by
  have := hc.fac (coconeOfChar f) j
  apply_fun (fun f ↦ f a) at this
  change hc.desc (coconeOfChar f) ((c.ι.app j) a) = _ at this
  simp only [descChar, AddEquiv.toAddMonoidHom_eq_coe, Functor.const_obj_obj, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply, Functor.comp_obj, uliftFunctor_obj, coe_of]
  conv_lhs => erw [this]
  rfl

lemma descChar_uniq (f : lc.pt →+ A) (m : c.pt →+ A) (hm : ∀ (j : J) (a : K.obj j),
    m (c.ι.app j a) = f ((lc.ι.app j {down := a}))) : m = descChar hc f := by
  refine AddMonoidHom.ext_iff.mpr (congrFun ?_)
  dsimp [descChar]
  rw [← AddEquiv.symm_comp_eq]
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp m = hc.desc (coconeOfChar f) by
    rw [← this]; rfl
  refine hc.uniq (coconeOfChar f) ((@AddEquiv.ulift A _).symm.toAddMonoidHom.comp m) (fun j ↦ ?_)
  ext a
  change ({down := m (c.ι.app j a)} : ULift A) = _
  rw [hm j a]
  rfl

lemma descChar_comp (f : lc.pt →+ A) (g : A →+ A') :
    descChar hc (g.comp f) = g.comp (descChar hc f) := by
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp (descChar hc (g.comp f)) =
      (@AddEquiv.ulift A' _).symm.toAddMonoidHom.comp (g.comp (descChar hc f)) by
    ext a
    apply_fun (fun f ↦ f a) at this
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  refine (hc.uniq (coconeOfChar (g.comp f)) (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (g.comp (descChar hc f))) (fun j ↦ ?_)).symm
  ext a
  simp [coconeOfChar]
  conv_lhs => erw [descChar_fac hc f j a]
  rfl

lemma descChar_zero_eq_zero : descChar hc (0 : lc.pt →+ A) = 0 := by
  have heq : (0 : lc.pt →+ A) = (0 : Unit →+ A).comp (0 : lc.pt →+ Unit) := by
    ext _; simp
  rw [heq, descChar_comp]
  simp

variable {ι : Type*} (B : ι → Type) [∀ (i : ι), AddCommGroup (B i)]
    (f : (i : ι) → lc.pt →+ B i)

def descCharFamily : c.pt →+ ((i : ι) → B i) := Pi.addMonoidHom (fun i ↦ descChar hc (f i))

lemma descCharFamily_comp (g : ((i : ι) → B i) →+ A) :
    descChar hc (g.comp (Pi.addMonoidHom f)) = g.comp (descCharFamily hc B f) := by
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp (descChar hc (g.comp (Pi.addMonoidHom f))) =
      (@AddEquiv.ulift A _).symm.toAddMonoidHom.comp (g.comp (descCharFamily hc B f)) by
    ext a
    apply_fun (fun f ↦ f a) at this
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
      Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  refine (hc.uniq (coconeOfChar (g.comp (Pi.addMonoidHom f)))
    (AddEquiv.ulift.symm.toAddMonoidHom.comp (g.comp (descCharFamily hc B f)))
    (fun j ↦ ?_)).symm
  ext a
  simp [coconeOfChar]
  congr 1
  ext i
  simp [descCharFamily]
  conv_lhs => erw [descChar_fac hc (f i) j a]
  rfl

abbrev truc (C : Type*) [AddCommGroup C] :
    C →+ ((_ : CharacterModule C) → AddCircle (1 : ℚ)) where
  toFun a c := c a
  map_zero' := by ext _; simp
  map_add' _ _ := by ext _; simp

lemma truc_injective (C : Type*) [AddCommGroup C] : Function.Injective (truc C) := by
  refine (injective_iff_map_eq_zero _).mpr (fun a ha ↦ CharacterModule.eq_zero_of_character_apply
    (fun c ↦ ?_))
  apply_fun (fun f ↦ f c) at ha
  exact ha

variable (lc)

noncomputable def descHom : c.pt →+ lc.pt := by
  set u : lc.pt →+ ((c : CharacterModule lc.pt) → AddCircle (1 : ℚ)) := truc lc.pt
  set u' := descCharFamily hc (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ))
    (fun c ↦ c) with hdef'
  set π := (QuotientAddGroup.mk' (AddMonoidHom.range u)) with hπ
  have h : u.range = π.ker := (QuotientAddGroup.ker_mk' _).symm
  have h' : π.comp u' = 0 := by
    refine CharacterModule.hom_eq_zero_of_character_apply (fun c ↦ ?_)
    rw [← AddMonoidHom.comp_assoc, ← descCharFamily_comp hc
      (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) (fun c ↦ c)]
    convert descChar_zero_eq_zero hc
    ext a
    change (c.comp (π.comp u)) a = 0
    rw [(AddMonoidHom.range_le_ker_iff _ _).mp (le_of_eq h), c.comp_zero,
      AddMonoidHom.zero_apply]
  rw [← AddMonoidHom.range_le_ker_iff, ← h] at h'
  exact (AddMonoidHom.ofInjective (truc_injective lc.pt)).symm.toAddMonoidHom.comp
    ((AddSubgroup.inclusion h').comp (AddMonoidHom.rangeRestrict u'))

variable {lc}

lemma descHom_property (χ : lc.pt →+ AddCircle (1 : ℚ)) : χ.comp (descHom lc hc) =
    descChar hc χ := by
  change ((Pi.evalAddMonoidHom (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) χ).comp
    (truc lc.pt)).comp (descHom lc hc) = _
  refine AddMonoidHom.ext (fun a ↦ ?_)
  conv_lhs => rw [AddMonoidHom.comp_assoc, AddMonoidHom.comp_apply]
  erw [AddMonoidHom.apply_ofInjective_symm (f := truc lc.pt) (truc_injective lc.pt),
    AddMonoidHom.coe_rangeRestrict]
  conv_lhs => erw [← AddMonoidHom.comp_apply (Pi.evalAddMonoidHom (fun x ↦ AddCircle 1) χ)
                (descCharFamily hc (fun x ↦ AddCircle 1) fun c ↦ c)]
              rw [← descCharFamily_comp]
  rfl

lemma descHom_fac (j : J) (a : K.obj j) :
    descHom lc hc (c.ι.app j a) = lc.ι.app j {down := a} := by
  rw [← add_neg_eq_zero]
  refine CharacterModule.eq_zero_of_character_apply (fun χ ↦ ?_)
  rw [χ.map_add]
  change (χ.comp ((descHom lc hc).comp (c.ι.app j))) a + _ = 0
  rw [← AddMonoidHom.comp_assoc, descHom_property]
  erw [descChar_fac]
  simp

lemma descHom_uniq (m : c.pt →+ lc.pt) (hm : ∀ (j : J) (a : K.obj j),
    m (c.ι.app j a) = lc.ι.app j {down := a}) : m = descHom lc hc := by
  rw [← add_neg_eq_zero]
  refine CharacterModule.hom_eq_zero_of_character_apply (fun χ ↦ ?_)
  rw [AddMonoidHom.comp_add, AddMonoidHom.comp_neg, descHom_property, add_neg_eq_zero]
  refine descChar_uniq _ _ _ (fun j a ↦ ?_)
  simp only [Functor.const_obj_obj, AddMonoidHom.coe_comp, Function.comp_apply, Functor.comp_obj,
    uliftFunctor_obj, coe_of]
  erw [hm j a]
  rfl

end AddCommGrp

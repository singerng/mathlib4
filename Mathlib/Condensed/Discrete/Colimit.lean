/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.LocallyConstant
import Mathlib.Condensed.Equivalence
import Mathlib.Topology.Category.LightProfinite.Extend
/-!

# The condensed set given by left Kan extension from `FintypeCat` to `Profinite`.

This file provides the necessary API to prove that a condensed set `X` is discrete if and only if
for every profinite set `S = limᵢSᵢ`, `X(S) ≅ colimᵢX(Sᵢ)`, and the analogous result for light
condensed sets.
-/

universe u

noncomputable section

open CategoryTheory Functor Limits FintypeCat CompHausLike.LocallyConstant

attribute [local instance] ConcreteCategory.instFunLike

namespace Condensed

section LocallyConstantAsColimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone <| F ⋙ toProfinite) (X : Type (u+1))

/-- The presheaf on `Profinite` of locally constant functions to `X`. -/
abbrev locallyConstantPresheaf : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u+1}.obj X

/--
The functor `locallyConstantPresheaf` takes cofiltered limits of finite sets with surjective
projection maps to colimits.
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i) = fj.comap (c.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [comp_obj, op_obj, functorToPresheaves_obj_obj, CompHausLike.coe_of,
      Functor.comp_map, op_map, Quiver.Hom.unop_op, functorToPresheaves_obj_map]
    -- Note: we might want to remove the `simps` attribute from `FintypeCat.toProfinite`; keeping
    -- `toProfinite_obj` in the `dsimp` block above causes the following `ext` to fail.
    ext x
    obtain ⟨x, hx⟩ := ((Profinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

/-- `isColimitLocallyConstantPresheaf` in the case of `S.asLimit`. -/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : Profinite) :
    IsColimit <| (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

end LocallyConstantAsColimit

/--
Given a presheaf `F` on `Profinite`, `lanPresheaf F` is the left Kan extension of its
restriction to finite sets along the inclusion functor of finite sets into `Profinite`.
-/
abbrev lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

/--
To presheaves on `Profinite` whose restrictions to finite sets are isomorphic have isomorphic left
Kan extensions.
-/
def lanPresheafExt {F G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)}
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

@[simp]
lemma lanPresheafExt_hom {F G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.hom) := by
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom]
  rw [pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  intro j
  simp
  rfl

@[simp]
lemma lanPresheafExt_inv {F G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.inv) := by
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv]
  rw [pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  intro j
  simp
  rfl

variable {S : Profinite.{u}} {F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)}

instance : Final <| Profinite.Extend.functorOp S.asLimitCone :=
  Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

/--
A presheaf, which takes a profinite set written as a cofiltered limit to the corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

@[simp]
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheafIso hF).hom = colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

/-- `lanPresheafIso` is natural in `S`. -/
def lanPresheafNatIso (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    lanPresheaf F ≅ F :=
  NatIso.ofComponents (fun ⟨S⟩ ↦ (lanPresheafIso (hF S)))
    fun _ ↦ (by simpa using colimit.hom_ext fun _ ↦ (by simp))

@[simp]
lemma lanPresheafNatIso_hom_app (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
    (S : Profiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

lemma lanPresheafExt_trans_lanPresheafNatIso_hom_app {G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)}
    (i : toProfinite.op ⋙ G ≅ toProfinite.op ⋙ F)
    (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) (S : Profiniteᵒᵖ) :
    (lanPresheafExt i ≪≫ lanPresheafNatIso hF).hom.app S =
      colimit.desc (CostructuredArrow.proj toProfinite.op S ⋙ toProfinite.op ⋙ G)
    ((Cocones.precompose (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.hom)).obj
      (Profinite.Extend.cocone F (Opposite.unop S))) := by
  simp

/--
`lanPresheaf (locallyConstantPresheaf X)` is a sheaf for the coherent topology on `Profinite`.
-/
def lanSheafProfinite (X : Type (u+1)) : Sheaf (coherentTopology Profinite.{u}) (Type (u+1)) where
  val := lanPresheaf (locallyConstantPresheaf X)
  cond := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _)]
    exact ((CompHausLike.LocallyConstant.functor.{u, u+1}
      (hs := fun _ _ _ ↦ ((Profinite.effectiveEpi_tfae _).out 0 2).mp)).obj X).cond

/-- `lanPresheaf (locallyConstantPresheaf X)` as a condensed set. -/
def lanCondensedSet (X : Type (u+1)) : CondensedSet.{u} :=
  (ProfiniteCompHaus.equivalence _).functor.obj (lanSheafProfinite X)

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1))

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`Profinite`.
-/
@[simps]
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u+1) where
  obj X := X.unop → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)
  map f g := g ∘ f.unop

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
@[simps! hom_app]
def locallyConstantIsoFinYoneda :
    toProfinite.op ⋙ (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))) ≅
    finYoneda F :=
  NatIso.ofComponents fun Y ↦ {
    hom := fun f ↦ f.1
    inv := fun f ↦ ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/-- A finite set as a coproduct cocone in `Profinite` over itself. -/
def fintypeCatAsCofan (X : FintypeCat) : Cofan (fun (_ : X) ↦ toProfinite.obj (of (PUnit.{u+1}))) :=
  Cofan.mk (toProfinite.obj X) (fun x ↦ toProfinite.map (fun _ ↦ x))

/-- A finite set is the coproduct of its points in `Profinite`. -/
def fintypeCatAsCofanIsColimit (X : FintypeCat.{u}) :
    IsColimit (fintypeCatAsCofan X) :=
  mkCofanColimit _ (fun t ↦ ⟨fun x ↦ t.inj x PUnit.unit, continuous_bot⟩) (by aesop)
    (fun _ _ h ↦ by ext x; exact ContinuousMap.congr_fun (h x) _)

variable [PreservesFiniteProducts F]

noncomputable instance (X : FintypeCat.{u}) :
    PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Fintype X' := Fintype.ofEquiv X e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
def isoFinYonedaComponents (X : FintypeCat.{u}) :
    F.obj ((toProfinite.{u}.op.obj ⟨X⟩)) ≅ (X → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u+1} fun _ ↦ F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)).2

section

/-- A finite set as a coproduct cocone in `Profinite` over itself. -/
def fintypeCatAsCofan' (X : Profinite) [Fintype X] :
    Cofan (fun (_ : X) ↦ (Profinite.of (PUnit.{u+1}))) :=
  Cofan.mk X (fun x ↦ (ContinuousMap.const _ x))

/-- A finite set is the coproduct of its points in `Profinite`. -/
def fintypeCatAsCofanIsColimit' (X : Profinite) [Fintype X] :
    IsColimit (fintypeCatAsCofan' X) := by
  refine mkCofanColimit _ (fun t ↦ ⟨fun x ↦ t.inj x PUnit.unit, ?_⟩) ?_
    (fun _ _ h ↦ by ext x; exact ContinuousMap.congr_fun (h x) _)
  · convert continuous_bot
    simp [fintypeCatAsCofan']
    suffices DiscreteTopology X from this.1
    rw [discreteTopology_iff_forall_isClosed]
    intro s
    have : s = ⋃ x ∈ s, {x} := (Set.biUnion_of_singleton s).symm
    rw [this]
    apply Set.Finite.isClosed_biUnion
    · exact s.toFinite
    · exact fun _ _ ↦ isClosed_singleton
  · aesop

variable [PreservesFiniteProducts F]

noncomputable instance (X : Profinite) [Fintype X] :
    PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Fintype X' := Fintype.ofEquiv X e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
def isoFinYonedaComponents' (X : Profinite.{u}) [Fintype X] :
    F.obj ⟨X⟩ ≅ (X → F.obj ⟨Profinite.of PUnit.{u+1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit' X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u+1} fun _ ↦ F.obj ⟨Profinite.of PUnit.{u+1}⟩).2

end

/-- TODO: move -/
@[simps!]
def _root_.Profinite.element (S : Profinite.{u}) (s : S) : Profinite.of PUnit.{u+1} ⟶ S :=
  ContinuousMap.const _ s

lemma _root_.Profinite.element_comp {S T : Profinite.{u}} (s : S) (g : S ⟶ T) :
    S.element s ≫ g = T.element (g s) :=
  rfl

lemma _root_.Profinite.comp_element (S : Profinite.{u}) (s : S) :
    Profinite.isTerminalPUnit.from S ≫ S.element s = ContinuousMap.const _ s :=
  rfl

attribute [nolint simpNF] Profinite.element_apply

@[simp]
lemma isoFinYonedaComponents_hom_apply (X : FintypeCat.{u})
    (y : F.obj (toProfinite.{u}.op.obj ⟨X⟩)) (x : X) :
    (isoFinYonedaComponents F X).hom y x =
      F.map ((toProfinite.obj X).element x).op y := by
  rfl

@[simp]
lemma isoFinYonedaComponents'_hom_apply (X : Profinite.{u}) [Fintype X]
    (y : F.obj ⟨X⟩) (x : X) :
    (isoFinYonedaComponents' F X).hom y x =
      F.map (X.element x).op y := by
  rfl

-- @[simp]
-- lemma isoFinYonedaComponents_inv {X Y : FintypeCat.{u}} (g : Y ⟶ X)
--     (f : X → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :
--     ∃ x, F.map (toProfinite.map g).op ((isoFinYonedaComponents F X).inv f) =
--       F.map (Profinite.isTerminalPUnit.from _).op (f x) := by
--   -- have : toProfinite.map g ≫ Profinite.isTerminalPUnit.from (toProfinite.obj X) =
--   --   Profinite.isTerminalPUnit.from _ := by simp
--   -- rw [← this]
--   -- simp only [toProfinite_obj, op_obj, op_comp, FunctorToTypes.map_comp_apply]

--   -- apply congrArg
--   -- apply injective_of_mono (isoFinYonedaComponents F X).hom
--   -- simp only [op_obj, toProfinite_obj, CategoryTheory.inv_hom_id_apply]
--   -- ext x
--   -- simp only [op_obj, toProfinite_obj, isoFinYonedaComponents_hom_apply]
--   -- simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
--   -- rw [Profinite.element_comp]
--   -- simp
--   sorry



/--
The restriction of a finite product preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps!]
def isoFinYoneda : toProfinite.op ⋙ F ≅ finYoneda F :=
  letI : ∀ (X : FintypeCatᵒᵖ), Fintype (toProfinite.obj X.unop) :=
    fun X ↦ inferInstanceAs (Fintype X.unop)
  NatIso.ofComponents (fun X ↦ isoFinYonedaComponents' F (toProfinite.obj X.unop)) fun _ ↦ by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [toProfinite_obj, types_comp_apply, isoFinYonedaComponents'_hom_apply, finYoneda_map,
      op_obj, Function.comp_apply, ← FunctorToTypes.map_comp_apply]
    rfl

/--
A presheaf `F`, which takes a profinite set written as a cofiltered limit to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
def isoLocallyConstantOfIsColimit
    (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ (locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  (lanPresheafNatIso hF).symm ≪≫ lanPresheafExt
    (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

end Condensed

namespace LightCondensed

section LocallyConstantAsColimit

variable {F : ℕᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite) (X : Type u)

/-- The presheaf on `LightProfinite` of locally constant functions to `X`. -/
abbrev locallyConstantPresheaf : LightProfiniteᵒᵖ ⥤ Type u :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

/--
The functor `locallyConstantPresheaf` takes sequential limits of finite sets with surjective
projection maps to colimits.
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i) = fj.comap (c.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [comp_obj, op_obj, functorToPresheaves_obj_obj, CompHausLike.coe_of,
      Functor.comp_map, op_map, Quiver.Hom.unop_op, functorToPresheaves_obj_map]
    ext x
    obtain ⟨x, hx⟩ := ((LightProfinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

/-- `isColimitLocallyConstantPresheaf` in the case of `S.asLimit`. -/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : LightProfinite) :
    IsColimit <| (locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone) :=
  (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence ℕ).inverse _).symm
    (isColimitLocallyConstantPresheaf _ _ S.asLimit)

end LocallyConstantAsColimit

instance (S : LightProfinite.{u}ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow toLightProfinite.op S) (Type u) :=
  hasColimitsOfShape_of_equivalence (asEquivalence (CostructuredArrow.pre Skeleton.incl.op _ S))

/--
Given a presheaf `F` on `LightProfinite`, `lanPresheaf F` is the left Kan extension of its
restriction to finite sets along the inclusion functor of finite sets into `Profinite`.
-/
abbrev lanPresheaf (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

/--
To presheaves on `LightProfinite` whose restrictions to finite sets are isomorphic have isomorphic
left Kan extensions.
-/
abbrev lanPresheafExt {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u}
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

variable {S : LightProfinite.{u}} {F : LightProfinite.{u}ᵒᵖ ⥤ Type u}

instance : Final <| LightProfinite.Extend.functorOp S.asLimitCone :=
  LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

/--
A presheaf, which takes a light profinite set written as a sequential limit to the corresponding
colimit, agrees with the left Kan extension of its restriction.
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

@[simp]
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheafIso hF).hom = colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

/-- `lanPresheafIso` is natural in `S`. -/
def lanPresheafNatIso
    (hF : ∀ S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (lanPresheafIso (hF S))) fun _ ↦ ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_obj, pointwiseLeftKanExtension_map,
    lanPresheafIso_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ ↦ (by simp)

/--
`lanPresheaf (locallyConstantPresheaf X)` as a light condensed set.
-/
def lanLightCondSet (X : Type u) : LightCondSet.{u} where
  val := lanPresheaf (locallyConstantPresheaf X)
  cond := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _)]
    exact (CompHausLike.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ ↦ ((LightProfinite.effectiveEpi_iff_surjective _).mp)).obj X).cond

variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`LightProfinite`.
-/
@[simps]
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop → F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩)
  map f g := g ∘ f.unop

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
def locallyConstantIsoFinYoneda : toLightProfinite.op ⋙
    (locallyConstantPresheaf (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))) ≅ finYoneda F :=
  NatIso.ofComponents fun Y ↦ {
    hom := fun f ↦ f.1
    inv := fun f ↦ ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/-- A finite set as a coproduct cocone in `LightProfinite` over itself. -/
def fintypeCatAsCofan (X : FintypeCat) :
    Cofan (fun (_ : X) ↦ toLightProfinite.obj (of (PUnit.{u+1}))) :=
  Cofan.mk (toLightProfinite.obj X) (fun x ↦ toProfinite.map (fun _ ↦ x))

/-- A finite set is the coproduct of its points in `LightProfinite`. -/
def fintypeCatAsCofanIsColimit (X : FintypeCat.{u}) :
    IsColimit (fintypeCatAsCofan X) := by
  refine mkCofanColimit _ (fun t ↦ ⟨fun x ↦ t.inj x PUnit.unit, continuous_bot⟩) (by aesop) ?_
  intro t m h
  ext x
  change m x = t.inj x _
  rw [← h x]
  rfl

variable [PreservesFiniteProducts F]

noncomputable instance (X : FintypeCat.{u}) : PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Fintype X' := Fintype.ofEquiv X e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) F

/-- Auxiliary definition for `isoFinYoneda`. -/
@[simps!]
def isoFinYonedaComponents (X : FintypeCat.{u}) :
    F.obj ((toLightProfinite.{u}.op.obj ⟨X⟩)) ≅
      (X → F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
    (Types.productLimitCone.{u, u} fun _ ↦ F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩)).2

/--
The restriction of a finite product preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
def isoFinYoneda : toLightProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X ↦ isoFinYonedaComponents F X.unop) fun _ ↦ by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [types_comp_apply, isoFinYonedaComponents_hom, finYoneda_map, op_obj,
      Function.comp_apply, Types.productLimitCone, const_obj_obj, fintypeCatAsCofan, Cofan.mk_pt,
      cofan_mk_inj, Fan.mk_pt, Fan.mk_π_app, ← FunctorToTypes.map_comp_apply]
    rfl

/--
A presheaf `F`, which takes a light profinite set written as a sequential limit to the corresponding
colimit, is isomorphic to the presheaf `LocallyConstant - F(*)`.
-/
def isoLocallyConstantOfIsColimit (hF : ∀ S : LightProfinite, IsColimit <|
    F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
      F ≅ (locallyConstantPresheaf
        (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

end LightCondensed

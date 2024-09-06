import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.Discriminant

variable (K : Type*) [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Finset
  NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional MeasureTheory.Measure

open scoped Real ENNReal ComplexOrder

set_option linter.style.longFile 0

noncomputable section

namespace NumberField.mixedEmbedding

variable {K}

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

open Classical in
def negAt (s : Finset {w : InfinitePlace K // IsReal w}) :
    (E K) ≃L[ℝ] (E K) :=
  ContinuousLinearEquiv.prod (ContinuousLinearEquiv.piCongrRight
    fun w ↦ if w ∈ s then ContinuousLinearEquiv.neg ℝ else ContinuousLinearEquiv.refl ℝ ℝ)
      (ContinuousLinearEquiv.refl ℝ _)

theorem negAt_apply_of_isReal_and_mem  {s : Finset {w // IsReal w}} (x : E K)
    {w : {w // IsReal w}} (hw : w ∈ s) :
    (negAt s x).1 w = - x.1 w := by
  simp_rw [negAt, ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.piCongrRight_apply,
    if_pos hw, ContinuousLinearEquiv.neg_apply]

theorem negAt_apply_of_isReal_and_not_mem {s : Finset {w // IsReal w}} (x : E K)
    {w : {w // IsReal w}} (hw : w ∉ s) :
    (negAt s x).1 w = x.1 w := by
  simp_rw [negAt, ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.piCongrRight_apply,
    if_neg hw, ContinuousLinearEquiv.refl_apply]

theorem negAt_apply_of_isComplex (s : Finset {w // IsReal w}) (x : E K)
    (w : {w // IsComplex w})  :
    (negAt s x).2 w = x.2 w := rfl

theorem normAtPlace_negAt_eq (s : Finset {w // IsReal w}) (x : E K) (w : InfinitePlace K) :
    normAtPlace w (negAt s x) = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [normAtPlace_apply_isReal hw]
    · by_cases hw' : ⟨w, hw⟩ ∈ s
      · rw [negAt_apply_of_isReal_and_mem _ hw', norm_neg]
      · rw [negAt_apply_of_isReal_and_not_mem _ hw']
  · simp_rw [normAtPlace_apply_isComplex hw, negAt_apply_of_isComplex _ _ ⟨w, hw⟩]

open Classical in
theorem volume_preserving_negAt (s : Finset {w : InfinitePlace K // IsReal w}) :
    MeasurePreserving (negAt s) := by
  refine MeasurePreserving.prod (volume_preserving_pi fun w ↦ ?_) (MeasurePreserving.id _)
  by_cases hw : w ∈ s
  · simp_rw [if_pos hw]
    exact measurePreserving_neg _
  · simp_rw [if_neg hw]
    exact MeasurePreserving.id _

theorem negAt_symm (s : Finset {w : InfinitePlace K // IsReal w}) :
    (negAt s).symm = negAt s := by
  ext x w
  · by_cases h : w ∈ s
    · simp_rw [negAt, ContinuousLinearEquiv.prod_symm, ContinuousLinearEquiv.prod_apply,
        ContinuousLinearEquiv.piCongrRight_symm_apply, ContinuousLinearEquiv.piCongrRight_apply,
        if_pos h, ContinuousLinearEquiv.symm_neg]
    · simp_rw [negAt, ContinuousLinearEquiv.prod_symm, ContinuousLinearEquiv.prod_apply,
        ContinuousLinearEquiv.piCongrRight_symm_apply, ContinuousLinearEquiv.piCongrRight_apply,
        if_neg h, ContinuousLinearEquiv.refl_symm]
  · rfl

variable (A : Set (E K)) (hA₁ : MeasurableSet A) (hA₂ : ∀ s, negAt s '' A ⊆ A)

abbrev plusPart : Set (E K) := A ∩ {x | ∀ w, 0 < x.1 w}

include hA₁ in
theorem measurableSet_plusPart :
    MeasurableSet (plusPart A) := by
  convert_to MeasurableSet (A ∩ (⋂ w, {x | 0 < x.1 w}))
  · ext; simp
  · refine MeasurableSet.inter hA₁ ?_
    refine MeasurableSet.iInter fun _ ↦ ?_
    exact measurableSet_lt measurable_const ((measurable_pi_apply _).comp'  measurable_fst)

abbrev negAtPlus (s : Finset {w : InfinitePlace K // IsReal w}) : Set (E K) :=
    negAt s '' (plusPart A)

include hA₁ in
theorem measurableSet_negAtPlus (s : Finset {w : InfinitePlace K // IsReal w}) :
    MeasurableSet (negAtPlus A s) := by
  rw [negAtPlus, ← negAt_symm, ContinuousLinearEquiv.image_symm_eq_preimage]
  exact (measurableSet_plusPart A hA₁).preimage (negAt s).continuous.measurable

theorem negAtPlus_neg_of_mem {s : Finset {w // IsReal w}} {x : E K} (hx : x ∈ negAtPlus A s)
    {w : {w // IsReal w}} (hw : w ∈ s) :
    x.1 w < 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_of_isReal_and_mem _ hw, neg_lt_zero]
  exact hy.2 w

theorem negAtPlus_pos_of_not_mem {s : Finset {w // IsReal w}} {x : E K} (hx : x ∈ negAtPlus A s)
    {w : {w // IsReal w}} (hw : w ∉ s) :
    0 < x.1 w := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [negAt_apply_of_isReal_and_not_mem _ hw]
  exact hy.2 w

-- Use this to golf proofs?
theorem negAtPlus_eq_preimage (s : Finset {w // IsReal w} ) :
    negAtPlus A s = negAt s ⁻¹' (plusPart A) := by
  rw [← negAt_symm, ← ContinuousLinearEquiv.image_eq_preimage]

theorem res1 : Pairwise (Disjoint on (negAtPlus A)) := by
  classical
  intro s t hst
  have : ∃ w, (w ∈ s ∧ w ∉ t) ∨ (w ∈ t ∧ w ∉ s) := by
    obtain ⟨w, hw⟩ := Finset.symmDiff_nonempty.mpr hst
    refine ⟨w, ?_⟩
    obtain h | h := Finset.mem_union.mp hw
    · left
      rwa [← Finset.mem_sdiff]
    · right
      rwa [← Finset.mem_sdiff]
  obtain ⟨w, hw⟩ := this
  refine Set.disjoint_left.mpr fun _ hx hx' ↦ ?_
  obtain hw | hw := hw
  · exact lt_irrefl _ <|
      (negAtPlus_neg_of_mem A hx hw.1).trans (negAtPlus_pos_of_not_mem A hx' hw.2)
  · exact lt_irrefl _ <|
      (negAtPlus_neg_of_mem A hx' hw.1).trans (negAtPlus_pos_of_not_mem A hx hw.2)

include hA₂ in
theorem res211 (s) : negAtPlus A s ⊆ A := by
  rintro _ ⟨x, hx, rfl⟩
  exact hA₂ s (Set.mem_image_of_mem (negAt s) hx.1)

open Classical in
def signSet (x : E K) : Finset {w : InfinitePlace K // IsReal w} :=
  Set.toFinset (fun w ↦ x.1 w ≤ 0)

theorem mem_signSet {x : E K} {w : {w // IsReal w}} :
    w ∈ signSet x ↔ x.1 w ≤ 0 := by
  simp_rw [signSet, Set.mem_toFinset, Set.mem_def]

theorem negAt_signSet_apply (x : E K) :
    negAt (signSet x) x = (fun w ↦ |x.1 w|, x.2) := by
  ext w
  · by_cases hw : w ∈ signSet x
    · simp_rw [negAt_apply_of_isReal_and_mem _ hw, abs_of_nonpos (mem_signSet.mp hw)]
    · simp_rw [negAt_apply_of_isReal_and_not_mem _ hw, abs_of_pos
        (lt_of_not_ge (mem_signSet.not.mp hw))]
  · rfl

include hA₂ in
theorem res22 {x : E K} (hx : x ∈ A) (hx' : ∀ w, x.1 w ≠ 0) :
    x ∈ negAtPlus A (signSet x) := by
  rw [negAtPlus, ← negAt_symm, ContinuousLinearEquiv.image_symm_eq_preimage, Set.mem_preimage]
  refine Set.mem_inter ?_ ?_
  · exact (hA₂ (signSet x)) (Set.mem_image_of_mem _ hx)
  · rw [negAt_signSet_apply]
    exact fun w ↦ abs_pos.mpr (hx' w)

abbrev part₀ : Set (E K) := A ∩ (⋃ w, {x | x.1 w = 0})

include hA₂ in
theorem res21 : A = (⋃ s, negAtPlus A s) ∪ part₀ A := by
  refine Set.Subset.antisymm_iff.mpr ⟨fun x hx ↦ ?_,
    Set.union_subset (Set.iUnion_subset fun _ ↦ res211 A hA₂ _) Set.inter_subset_left⟩
  by_cases hw : ∃ w, x.1 w = 0
  · refine Set.mem_union_right _ ?_
    refine Set.mem_inter hx ?_
    exact Set.mem_iUnion.mpr hw
  · refine Set.mem_union_left _ ?_
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact signSet x
    · exact res22 A hA₂ hx (not_exists.mp hw)

open Classical in
theorem volume_eq_zero (w : {w // IsReal w}):
    volume ({x : E K | x.1 w = 0}) = 0 := by
  let A : AffineSubspace ℝ (E K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x.1 w = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  have : 1 ∈ A := h ▸ Set.mem_univ _
  simp [A] at this

open Classical in
theorem volume_part₀ :
    volume (part₀ A) = 0 :=
  measure_mono_null Set.inter_subset_right (measure_iUnion_null_iff.mpr fun _ ↦ volume_eq_zero _)

open Classical in
include hA₂ in
theorem res2 : A =ᵐ[volume] ⋃ s, negAtPlus A s := by
  convert union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr (volume_part₀ A))
  exact res21 A hA₂

include hA₁ in
open Classical in
theorem res3 (s) : volume (negAtPlus A s) = volume (plusPart A) := by
  rw [negAtPlus, ← negAt_symm, ContinuousLinearEquiv.image_symm_eq_preimage,
    (volume_preserving_negAt s).measure_preimage (measurableSet_plusPart A hA₁).nullMeasurableSet]

include hA₁ hA₂ in
open Classical in
theorem main : volume A = 2 ^ NrRealPlaces K * volume (plusPart A) := by
  rw [ measure_congr (res2 A hA₂), measure_iUnion]
  · simp_rw [res3 _ hA₁]
    rw [tsum_fintype, Finset.sum_const, ← Fintype.card, Fintype.card_finset, NrRealPlaces,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  · exact res1 A
  · exact fun _ ↦ measurableSet_negAtPlus A hA₁ _

namespace fundamentalCone

def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def realToMixed : (InfinitePlace K → ℝ) →L[ℝ] (E K) := ContinuousLinearMap.prod
  (ContinuousLinearMap.pi fun w ↦ ContinuousLinearMap.proj w.val)
  (ContinuousLinearMap.pi fun w ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj w.val))

@[simp]
theorem realToMixed_apply_of_isReal (x : InfinitePlace K → ℝ) {w : InfinitePlace K}
    (hw : IsReal w) :
    (realToMixed x).1 ⟨w, hw⟩ = x w := rfl

@[simp]
theorem realToMixed_apply_of_isComplex (x : InfinitePlace K → ℝ) {w : InfinitePlace K}
    (hw : IsComplex w) :
    (realToMixed x).2 ⟨w, hw⟩ = x w := rfl

@[simp]
theorem normAtPlace_realToMixed (w : InfinitePlace K) (x : InfinitePlace K → ℝ) :
    normAtPlace w (realToMixed x) = ‖x w‖ := by
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtPlace_apply_isReal hw, realToMixed]
  · simp [normAtPlace_apply_isComplex hw, realToMixed]

@[simp]
theorem norm_realToMixed (x : InfinitePlace K → ℝ) :
    mixedEmbedding.norm (realToMixed x) = ∏ w, ‖x w‖ ^ w.mult :=
  Finset.prod_congr rfl fun w _ ↦ by simp

theorem pos_norm_realToMixed {x : InfinitePlace K → ℝ} (hx : ∀ w, 0 < x w) :
    0 < mixedEmbedding.norm (realToMixed x) := by
  rw [norm_realToMixed]
  exact Finset.prod_pos fun w _ ↦ pow_pos (abs_pos_of_pos (hx w)) _

theorem logMap_realToMixed {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    logMap (realToMixed x) = fun w ↦ (mult w.val) * Real.log (x w.val) := by
  ext
  rw [logMap_apply_of_norm_one hx, normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

open Classical in
def mixedToReal (x : E K) : InfinitePlace K → ℝ :=
    fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖

theorem mixedToReal_apply_of_isReal {x : E K} {w : InfinitePlace K} (hw : IsReal w) :
    mixedToReal x w = x.1 ⟨w, hw⟩ := by
  rw [mixedToReal, dif_pos hw]

theorem mixedToReal_apply_of_isComplex {x : E K} {w : InfinitePlace K} (hw : IsComplex w) :
    mixedToReal x w = ‖x.2 ⟨w, hw⟩‖ := by
  rw [mixedToReal, dif_neg (not_isReal_iff_isComplex.mpr hw)]

-- def vectorNormAtPlace (x : E K) : InfinitePlace K → ℝ := fun w ↦ normAtPlace w x

theorem mixedToReal_smul (x : E K) {r : ℝ} (hr : 0 ≤ r) :
    mixedToReal (r • x) = r • mixedToReal x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [Pi.smul_apply, mixedToReal_apply_of_isReal hw, Prod.smul_fst, Pi.smul_apply]
  · simp_rw [Pi.smul_apply, mixedToReal_apply_of_isComplex hw, Prod.smul_snd, Pi.smul_apply,
      _root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, smul_eq_mul]

-- theorem vectorNormAtPlace_smul (x : E K) {r : ℝ} (hr : 0 ≤ r) :
--     vectorNormAtPlace (r • x) = r • vectorNormAtPlace x := by
--   ext
--   rw [vectorNormAtPlace, Pi.smul_apply, vectorNormAtPlace, normAtPlace_smul, smul_eq_mul,
--     abs_of_nonneg hr]

theorem mixedToRealToMixed (x : E K) :
    realToMixed (mixedToReal x) = (fun w ↦ x.1 w, fun w ↦ (‖x.2 w‖ : ℂ)) := by
  ext w
  · rw [realToMixed_apply_of_isReal, mixedToReal_apply_of_isReal]
  · rw [realToMixed_apply_of_isComplex, mixedToReal_apply_of_isComplex]

@[simp]
theorem norm_mixedToReal (x : E K) (w : InfinitePlace K) :
    ‖mixedToReal x w‖ = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal hw, normAtPlace_apply_isReal]
  · rw [mixedToReal_apply_of_isComplex hw, normAtPlace_apply_isComplex, norm_norm]

-- @[simp]
-- theorem norm_realToMixed_vectorNormAtPlace (x : E K) :
--     mixedEmbedding.norm (realToMixed (vectorNormAtPlace x)) = mixedEmbedding.norm x := by
--   simp_rw [norm_realToMixed, vectorNormAtPlace, mixedEmbedding.norm_apply, Real.norm_eq_abs,
--     abs_of_nonneg (normAtPlace_nonneg _ _)]

@[simp]
theorem norm_mixedToRealToMixed (x : E K) :
    mixedEmbedding.norm (realToMixed (mixedToReal x)) = mixedEmbedding.norm x := by
  simp_rw [norm_realToMixed, norm_mixedToReal, mixedEmbedding.norm_apply]

-- @[simp]
-- theorem logMap_realToMixed_vectorNormAtPlace_of_norm_one {x : E K}
--     (hx : mixedEmbedding.norm x = 1) :
--     logMap (realToMixed (vectorNormAtPlace x)) = logMap x := by
--   ext
--   rw [logMap_apply_of_norm_one hx, logMap_apply_of_norm_one
--     (by rwa [norm_realToMixed_vectorNormAtPlace]), normAtPlace_realToMixed, Real.norm_eq_abs,
--     Real.log_abs, vectorNormAtPlace]

@[simp]
theorem logMap_mixedToRealToMixed_of_norm_one {x : E K}
    (hx : mixedEmbedding.norm x = 1) :
    logMap (realToMixed (mixedToReal x)) = logMap x := by
  ext
  rw [logMap_apply_of_norm_one hx, logMap_apply_of_norm_one (by rwa [norm_mixedToRealToMixed]),
    normAtPlace_realToMixed, ← norm_mixedToReal]

-- theorem vectorNormAtPlace_realToMixed_of_nonneg {x : InfinitePlace K → ℝ} (hx : ∀ w, 0 ≤ x w) :
--     vectorNormAtPlace (realToMixed x) = x := by
--   ext
--   rw [vectorNormAtPlace, normAtPlace_realToMixed, Real.norm_eq_abs, abs_of_nonneg (hx _)]

@[simp]
theorem realToMixedToReal_eq_self_of_nonneg {x : InfinitePlace K → ℝ}
    (hx : ∀ w, IsComplex w → 0 ≤ x w) :
    mixedToReal (realToMixed x) = x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal hw, realToMixed_apply_of_isReal]
  · rw [mixedToReal_apply_of_isComplex hw, realToMixed_apply_of_isComplex, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hx w hw)]

variable (K)

open Classical in
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀_aux :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c w ↦ if hw : w = w₀ then
      Real.exp (- ((w₀ : InfinitePlace K).mult : ℝ)⁻¹ * ∑ w : {w // w ≠ w₀}, c w)
    else Real.exp ((w.mult : ℝ)⁻¹ * c ⟨w, hw⟩)
  invFun := fun x w ↦ w.val.mult * Real.log (x w.val)
  source := Set.univ
  target := {x | ∀ w, 0 < x w} ∩ {x | ∑ w, w.mult * Real.log (x w) = 0}
  map_source' _ _ := by
    dsimp only
    refine ⟨Set.mem_setOf.mpr fun w ↦ by split_ifs <;> exact Real.exp_pos _, ?_⟩
    simp_rw [Set.mem_setOf_eq, ← Finset.univ.sum_erase_add _ (Finset.mem_univ w₀), dif_pos]
    rw [Finset.sum_subtype _ (by aesop : ∀ w, w ∈ Finset.univ.erase w₀ ↔ w ≠ w₀)]
    conv_lhs => enter [1,2,w]; rw [dif_neg w.prop]
    simp_rw [Real.log_exp, neg_mul, mul_neg, mul_inv_cancel_left₀ mult_coe_ne_zero,
      add_neg_eq_zero]
    infer_instance
  map_target' _ _ := trivial
  left_inv' := by
    intro x _
    dsimp only
    ext w
    rw [dif_neg w.prop, Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' := by
    intro x hx
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, ← Finset.sum_subtype _
        (by aesop : ∀ w, w ∈ Finset.univ.erase w₀ ↔ w ≠ w₀) (fun w ↦ w.mult * Real.log (x w))]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ w₀), hx.2, _root_.zero_sub, neg_mul, mul_neg,
        neg_neg, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w₀)]
    · rw [dif_neg hw, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w)]

theorem mapToUnitsPow₀_aux_symm_apply (x : InfinitePlace K → ℝ) :
    (mapToUnitsPow₀_aux K).symm x = fun w ↦ w.val.mult * Real.log (x w.val) := rfl

theorem continuous_mapToUnitsPow₀_aux :
    Continuous (mapToUnitsPow₀_aux K) := by
  unfold mapToUnitsPow₀_aux
  refine continuous_pi_iff.mpr fun w ↦ ?_
  by_cases hw : w = w₀
  · simp_rw [dif_pos hw]
    fun_prop
  · simp_rw [dif_neg hw]
    fun_prop

theorem continuousOn_mapToUnitsPow₀_aux_symm :
    ContinuousOn (mapToUnitsPow₀_aux K).symm {x | ∀ w, x w ≠ 0} :=
  continuousOn_pi.mpr fun w ↦
    continuousOn_const.mul <| (continuousOn_apply _ _).log fun _ h ↦ h w

theorem pos_fundSystem (w : InfinitePlace K) (i : Fin (rank K)) :
    0 < w (fundSystem K i) := by
  refine pos_iff.mpr ?_
  simp only [ne_eq, RingOfIntegers.coe_eq_zero_iff, Units.ne_zero, not_false_eq_true]

open Classical in
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀ :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (InfinitePlace K → ℝ) :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
    equivFinRank).equivFun.symm.toEquiv.toPartialEquiv.trans (mapToUnitsPow₀_aux K)

theorem mapToUnitsPow₀_source :
    (mapToUnitsPow₀ K).source = Set.univ := by simp [mapToUnitsPow₀, mapToUnitsPow₀_aux]

theorem mapToUnitsPow₀_target :
    (mapToUnitsPow₀ K).target = {x | (∀ w, 0 < x w) ∧ mixedEmbedding.norm (realToMixed x) = 1} := by
  rw [mapToUnitsPow₀, mapToUnitsPow₀_aux]
  dsimp
  ext x
  simp_rw [Set.inter_univ, Set.mem_inter_iff, Set.mem_setOf, and_congr_right_iff]
  intro hx
  rw [← Real.exp_injective.eq_iff, Real.exp_zero, Real.exp_sum, norm_realToMixed]
  refine Eq.congr (Finset.prod_congr rfl fun _ _ ↦ ?_) rfl
  rw [← Real.log_rpow (hx _), Real.exp_log (Real.rpow_pos_of_pos (hx _) _), Real.norm_eq_abs,
    abs_of_pos (hx _), Real.rpow_natCast]

theorem norm_mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (realToMixed (mapToUnitsPow₀ K c)) = 1 := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.2
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

theorem mapToUnitsPow₀_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < mapToUnitsPow₀ K c w := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.1 w
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

theorem mapToUnitsPow₀_aux_symm_apply_of_norm_one {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    (mapToUnitsPow₀_aux K).symm x = logMap (realToMixed x) := by
  ext
  rw [logMap_apply_of_norm_one hx, normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]
  rfl

open Classical in
theorem mapToUnitsPow₀_symm_apply_of_norm_one {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) (i : Fin (rank K)) :
    (mapToUnitsPow₀ K).symm x (equivFinRank i) =
      ((basisUnitLattice K).ofZlatticeBasis ℝ (unitLattice K)).repr
        (logMap (realToMixed x)) i := by
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, Function.comp_apply,
    mapToUnitsPow₀_aux_symm_apply, EquivLike.coe_coe, Basis.equivFun_apply, Basis.repr_reindex,
    Finsupp.mapDomain_equiv_apply, logMap_realToMixed hx, Equiv.symm_apply_apply]

open Classical in
theorem mapToUnitsPow₀_symm_prod_fundSystem_rpow (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    (mapToUnitsPow₀ K).symm (fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i) = c := by
  ext
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, Function.comp_apply,
    mapToUnitsPow₀_aux_symm_apply, EquivLike.coe_coe, Basis.equivFun_apply, Basis.repr_reindex,
    Real.log_prod _ _ (fun _ _ ↦ ne_of_gt (Real.rpow_pos_of_pos (pos_fundSystem K _ _) _)),
    Real.log_rpow (pos_fundSystem K _ _), Finset.mul_sum, mul_left_comm,
    ← logEmbedding_component, logEmbedding_fundSystem, ← sum_fn, _root_.map_sum, ← smul_eq_mul,
    ← Pi.smul_def, _root_.map_smul, Finsupp.mapDomain_equiv_apply, Finset.sum_apply',
    Finsupp.coe_smul, Pi.smul_apply, Basis.ofZlatticeBasis_repr_apply, Basis.repr_self,
    smul_eq_mul, Finsupp.single_apply, Int.cast_ite, mul_ite, Int.cast_zero, mul_zero,
    EmbeddingLike.apply_eq_iff_eq, sum_ite_eq', mem_univ, if_true, Int.cast_one, mul_one]

open Classical in
theorem norm_realToMixed_prod_fundSystem_rpow (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (realToMixed fun w : InfinitePlace K ↦
      ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i) = 1 :=
   calc
    _ = |∏ w : InfinitePlace K,
          ∏ i, (w (fundSystem K (equivFinRank.symm i)) ^ c i) ^ w.mult| := by
      simp_rw [norm_realToMixed, Real.norm_eq_abs, ← abs_pow, ← Finset.abs_prod, ← Finset.prod_pow]
    _ = |∏ w : InfinitePlace K,
          ∏ i, (w (fundSystem K (equivFinRank.symm i)) ^ w.mult) ^ c i| := by
      congr!
      rw [← Real.rpow_natCast, Real.rpow_comm (pos_fundSystem K _ _).le, Real.rpow_natCast]
    _ = |∏ i,
          (∏ w : InfinitePlace K, (w (fundSystem K (equivFinRank.symm i)) ^ w.mult)) ^ c i| := by
      rw [Finset.prod_comm]
      simp_rw [Real.finset_prod_rpow _ _ (fun _ _ ↦ pow_nonneg (pos_fundSystem K _ _).le _)]
    _ = 1 := by
      simp_rw [prod_eq_abs_norm, Units.norm, Rat.cast_one, Real.one_rpow, prod_const_one, abs_one]

open Classical in
theorem mapToUnitsPow₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i := by
  refine (PartialEquiv.eq_symm_apply _ (by trivial) ?_).mp
    (mapToUnitsPow₀_symm_prod_fundSystem_rpow K c).symm
  rw [mapToUnitsPow₀_target]
  refine ⟨?_, norm_realToMixed_prod_fundSystem_rpow K c⟩
  exact fun _ ↦ Finset.prod_pos fun _ _ ↦ Real.rpow_pos_of_pos (pos_fundSystem K _ _) _

theorem realToMixed_mapToUnitsPow₀_mem_fundamentalCone_iff
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    realToMixed (mapToUnitsPow₀ K c) ∈ fundamentalCone K ↔ ∀ i, c i ∈ Set.Ico 0 1 := by
  classical
  simp_rw [mem_fundamentalCone, Zspan.mem_fundamentalDomain, ← mapToUnitsPow₀_symm_apply_of_norm_one
    K (norm_mapToUnitsPow₀ K _), (mapToUnitsPow₀ K).left_inv (by trivial), mapToUnitsPow₀_apply,
    norm_realToMixed_prod_fundSystem_rpow, and_iff_left one_ne_zero, Equiv.forall_congr_right
    (q := fun i ↦ c i ∈ Set.Ico 0 1)]

theorem mixedToReal_normEqOne_eq :
    mixedToReal '' (normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) =
      mapToUnitsPow₀ K '' (Set.univ.pi fun _ ↦ Set.Ico 0 1) := by
  classical
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨x, ⟨⟨⟨hx, hx₁⟩, hx₂⟩, hx₃⟩, rfl⟩
    rw [Set.mem_preimage, Zspan.mem_fundamentalDomain] at hx
    refine ⟨(mapToUnitsPow₀ K).symm (mixedToReal x), ?_, ?_⟩
    · rw [Set.mem_univ_pi]
      intro i
      rw [← equivFinRank.apply_symm_apply i, mapToUnitsPow₀_symm_apply_of_norm_one K (by
        rwa [norm_mixedToRealToMixed]), logMap_mixedToRealToMixed_of_norm_one hx₂]
      exact hx (equivFinRank.symm i)
    · rw [PartialEquiv.right_inv]
      rw [mapToUnitsPow₀_target]
      refine ⟨?_, ?_⟩
      · intro w
        obtain hw | hw := isReal_or_isComplex w
        · rw [mixedToReal_apply_of_isReal hw]
          exact hx₃ ⟨w, hw⟩
        · rw [mixedToReal_apply_of_isComplex hw, ← normAtPlace_apply_isComplex hw]
          refine lt_iff_le_and_ne.mpr ⟨normAtPlace_nonneg _ _,
            (mixedEmbedding.norm_ne_zero_iff.mp hx₁ w).symm⟩
      · rwa [norm_mixedToRealToMixed]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨realToMixed (mapToUnitsPow₀ K c), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [mem_fundamentalCone]
      refine ⟨?_, ?_⟩
      · rw [Zspan.mem_fundamentalDomain]
        intro _
        rw [← mapToUnitsPow₀_symm_apply_of_norm_one]
        · rw [PartialEquiv.left_inv]
          exact hc _ trivial
          trivial
        · exact norm_mapToUnitsPow₀ K c
      · rw [norm_mapToUnitsPow₀]
        exact one_ne_zero
    · exact norm_mapToUnitsPow₀ K c
    · intro _
      exact mapToUnitsPow₀_pos K c _
    · rw [realToMixedToReal_eq_self_of_nonneg]
      exact fun _ _ ↦ (mapToUnitsPow₀_pos K c _).le

-- Use the above to golf this proof
-- theorem vectorNormAtPlace_normEqOne_eq_image :
--     vectorNormAtPlace '' (normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) =
--       mapToUnitsPow₀ K '' (Set.univ.pi fun _ ↦ Set.Ico 0 1) := by
--   classical
--   ext x
--   refine ⟨?_, ?_⟩
--   · rintro ⟨x, ⟨⟨⟨hx, hx₁⟩, hx₂⟩, _⟩, rfl⟩
--     rw [Set.mem_preimage, Zspan.mem_fundamentalDomain] at hx
--     refine ⟨fun i ↦
--       (((basisUnitLattice K).ofZlatticeBasis ℝ (unitLattice K) ).repr (logMap x))
--         (equivFinRank.symm i), ?_, ?_⟩
--     · exact fun i _ ↦ hx (equivFinRank.symm i)
--     · rw [← logMap_realToMixed_vectorNormAtPlace_of_norm_one hx₂]
--       rw [← norm_realToMixed_vectorNormAtPlace] at hx₂
--       simp_rw [← mapToUnitsPow₀_symm_apply_of_norm_one (x := vectorNormAtPlace x) hx₂,
--         Equiv.apply_symm_apply]
--       rw [PartialEquiv.right_inv]
--       rw [mapToUnitsPow₀_target]
--       refine ⟨?_, hx₂⟩
--       intro _
--       rw [vectorNormAtPlace]
--       exact lt_iff_le_and_ne.mpr ⟨normAtPlace_nonneg _ _,
--         (mixedEmbedding.norm_ne_zero_iff.mp hx₁ _).symm⟩
--   · rintro ⟨c, hc, rfl⟩
--     refine ⟨realToMixed (mapToUnitsPow₀ K c), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
--     · rw [mem_fundamentalCone]
--       refine ⟨?_, ?_⟩
--       · rw [Zspan.mem_fundamentalDomain]
--         intro _
--         rw [← mapToUnitsPow₀_symm_apply_of_norm_one]
--         · rw [PartialEquiv.left_inv]
--           exact hc _ trivial
--           trivial
--         · exact norm_mapToUnitsPow₀ K c
--       · rw [norm_mapToUnitsPow₀]
--         exact one_ne_zero
--     · exact norm_mapToUnitsPow₀ K c
--     · intro _
--       exact mapToUnitsPow₀_pos K c _
--     · rw [vectorNormAtPlace_realToMixed_of_nonneg (fun _ ↦ (mapToUnitsPow₀_pos K c _).le)]

theorem mapToUnitsPow₀_ne_zero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact Function.ne_iff.mpr ⟨w, ne_of_gt (mapToUnitsPow₀_pos K c w)⟩

-- theorem mapToUnitsPow₀_symm_apply {x : InfinitePlace K → ℝ}
--     (hx : mixedEmbedding.norm (realToMixed x) = 1) :
--     (mapToUnitsPow₀_aux K).symm x = logMap (realToMixed x) := by
--   ext w
--   rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
--       normAtPlace_realToMixed, Real.log_abs]

open Classical in
theorem mapToUnitsPow₀_symm_apply {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    (mapToUnitsPow₀ K).symm x = (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
      equivFinRank).equivFun (logMap (realToMixed x)) := by
  rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, EquivLike.coe_coe, Function.comp_apply]
  congr with x
  rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
    normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

open Classical in
theorem continuous_mapToUnitsPow₀ :
    Continuous (mapToUnitsPow₀ K) := (continuous_mapToUnitsPow₀_aux K).comp <|
  LinearEquiv.continuous_symm _ (continuous_equivFun_basis _)

theorem continuousOn_mapToUnitsPow₀_symm :
    ContinuousOn (mapToUnitsPow₀ K).symm {x | ∀ w, x w ≠ 0} :=
  (continuous_equivFun_basis _).comp_continuousOn (continuousOn_mapToUnitsPow₀_aux_symm K)

open Classical in
@[simps source target]
def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w)
  invFun x w :=
    if hw : w = w₀ then mixedEmbedding.norm (realToMixed x) ^ (finrank ℚ K : ℝ)⁻¹ else
      (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
        equivFinRank).equivFun (logMap (realToMixed x)) ⟨w, hw⟩
  source := {x | 0 < x w₀}
  target := {x | ∀ w, 0 < x w}
  map_source' _ h _ :=by
    simp_rw [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (abs_pos.mpr (ne_of_gt h)) (mapToUnitsPow₀_pos K _ _)
  map_target' x hx := by
    refine Set.mem_setOf.mpr ?_
    dsimp only
    rw [dif_pos rfl]
    exact Real.rpow_pos_of_pos (pos_norm_realToMixed hx) _
  left_inv' _ h := by
    dsimp only
    ext w
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, _root_.map_smul, mixedEmbedding.norm_smul, norm_mapToUnitsPow₀, mul_one,
          ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀
          (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)), Real.rpow_one, abs_of_nonneg
          (abs_nonneg _), abs_of_pos (by convert h)]
    · rw [dif_neg hw, _root_.map_smul, logMap_smul (by rw [norm_mapToUnitsPow₀]; exact one_ne_zero)
        (abs_ne_zero.mpr (ne_of_gt h)), ← mapToUnitsPow₀_symm_apply K (norm_mapToUnitsPow₀ K _),
        PartialEquiv.left_inv _ (by rw [mapToUnitsPow₀_source]; trivial)]
  right_inv' x hx := by
    have h₀ : mixedEmbedding.norm
        (realToMixed (mixedEmbedding.norm (realToMixed x) ^ (- (finrank ℚ K : ℝ)⁻¹) • x)) = 1 := by
      rw [_root_.map_smul]
      refine norm_norm_rpow_smul_eq_one (ne_of_gt (pos_norm_realToMixed hx))
    dsimp only
    rw [dif_pos rfl]
    conv_lhs =>
      enter [2, 2, w]
      rw [dif_neg w.prop]
    ext w
    rw [Pi.smul_apply, ← logMap_smul]
    rw [← _root_.map_smul]
    rw [← mapToUnitsPow₀_symm_apply K h₀]
    rw [PartialEquiv.right_inv, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [abs_of_nonneg, Real.rpow_neg, mul_inv_cancel_left₀]
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx
    · exact mixedEmbedding.norm_nonneg (realToMixed x)
    · refine Real.rpow_nonneg ?_ _
      exact mixedEmbedding.norm_nonneg (realToMixed x)
    · rw [mapToUnitsPow₀_target]
      refine ⟨fun w ↦ ?_, h₀⟩
      exact mul_pos (Real.rpow_pos_of_pos (pos_norm_realToMixed hx) _) (hx w)
    · exact ne_of_gt (pos_norm_realToMixed hx)
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx
  open_source := isOpen_lt continuous_const (continuous_apply w₀)
  open_target := by
    convert_to IsOpen (⋂ w, {x : InfinitePlace K → ℝ | 0 < x w})
    · ext; simp
    · exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  continuousOn_toFun := ContinuousOn.smul (by fun_prop) <|
    (continuous_mapToUnitsPow₀ K).comp_continuousOn' (by fun_prop)
  continuousOn_invFun := by
    simp only
    rw [continuousOn_pi]
    intro w
    by_cases hw : w = w₀
    · simp_rw [hw, dite_true]
      refine Continuous.continuousOn ?_
      refine Continuous.rpow_const ?_ ?_
      · refine Continuous.comp' ?_ ?_
        exact mixedEmbedding.continuous_norm K
        exact ContinuousLinearMap.continuous realToMixed
      · intro _
        right
        rw [inv_nonneg]
        exact Nat.cast_nonneg' (finrank ℚ K)
    · simp_rw [dif_neg hw]
      refine Continuous.comp_continuousOn' (continuous_apply _) <|
        (continuous_equivFun_basis _).comp_continuousOn' ?_
      refine ContinuousOn.comp'' (continuousOn_logMap) ?_ ?_
      refine Continuous.continuousOn ?_
      exact ContinuousLinearMap.continuous realToMixed
      intro x hx
      refine ne_of_gt ?_
      exact pos_norm_realToMixed hx

theorem mapToUnitsPow_apply (c : InfinitePlace K → ℝ) :
    mapToUnitsPow K c = |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w) := rfl

open Classical in
-- Use this to simplify the definition of mapToUnitsPow?
abbrev mapToUnitsPow_single (c : InfinitePlace K → ℝ) : InfinitePlace K → (InfinitePlace K → ℝ) :=
  fun i ↦ if hi : i = w₀ then fun _ ↦ |c w₀| else
    fun w ↦ (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ (c i)

open Classical in
theorem mapToUnitsPow₀_eq_prod_single (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    mapToUnitsPow₀ K (fun w ↦ c w.val) w =
      ∏ i ∈ univ.erase w₀, mapToUnitsPow_single K c i w := by
  rw [mapToUnitsPow₀_apply, Finset.prod_subtype (Finset.univ.erase w₀)
    (fun w ↦ (by aesop : w ∈ univ.erase w₀ ↔ w ≠ w₀))]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [mapToUnitsPow_single, dif_neg w.prop]

theorem mapToUnitsPow_eq_prod_single (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    mapToUnitsPow K c w = ∏ i, mapToUnitsPow_single K c i w := by
  classical
  rw [← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀), mapToUnitsPow_apply, Pi.smul_apply,
    mapToUnitsPow₀_eq_prod_single, smul_eq_mul, mapToUnitsPow_single, dif_pos rfl]

theorem mapToUnitsPow_nonneg (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    0 ≤ mapToUnitsPow K c w :=
  mul_nonneg (abs_nonneg _) (mapToUnitsPow₀_pos K _ _).le

variable {K} in
theorem mapToUnitsPow_zero_iff {c : InfinitePlace K → ℝ} {w : InfinitePlace K} :
    mapToUnitsPow K c w = 0 ↔ c w₀ = 0 := by
  rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul, mul_eq_zero, abs_eq_zero,
    or_iff_left (ne_of_gt (mapToUnitsPow₀_pos K _ _))]

variable {K} in
theorem mapToUnitsPow_zero_iff' {c : InfinitePlace K → ℝ} :
    mapToUnitsPow K c = 0 ↔ c w₀ = 0 := by
  rw [mapToUnitsPow_apply, smul_eq_zero, abs_eq_zero, or_iff_left (mapToUnitsPow₀_ne_zero _ _)]

theorem mapToUnitsPow_pos {c : InfinitePlace K → ℝ} (hc : c w₀ ≠ 0) (w : InfinitePlace K) :
    0 < mapToUnitsPow K c w :=
  lt_of_le_of_ne (mapToUnitsPow_nonneg K c w) (Ne.symm (mapToUnitsPow_zero_iff.not.mpr hc))

theorem continuous_mapToUnitsPow :
    Continuous (mapToUnitsPow K) :=
  Continuous.smul (by fun_prop) ((continuous_mapToUnitsPow₀ K).comp' (by fun_prop))

theorem measurable_mapToUnitsPow_symm :
    Measurable (mapToUnitsPow K).symm := by
  classical
  dsimp [mapToUnitsPow, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk]
  refine measurable_pi_iff.mpr fun _ ↦ ?_
  split_ifs
  · refine Measurable.pow_const ?_ _
    exact Measurable.comp' (mixedEmbedding.continuous_norm K).measurable realToMixed.measurable
  · exact Measurable.eval <|
      (continuous_equivFun_basis ((Basis.ofZlatticeBasis ℝ (unitLattice K)
        (basisUnitLattice K)).reindex equivFinRank)).measurable.comp'
        (measurable_logMap.comp' realToMixed.measurable)

theorem mapToUnitsPow_image_minus_image_inter_aux {s : Set (InfinitePlace K → ℝ)}
    (hs : s ⊆ {x | 0 ≤ x w₀}) :
    s \ (s ∩ {x | 0 < x w₀}) ⊆ {x | x w₀ = 0} := by
  refine fun _ h ↦ eq_of_ge_of_not_gt (hs h.1) ?_
  have := h.2
  simp_rw [Set.mem_inter_iff, not_and, h.1, true_implies] at this
  exact this

theorem mapToUnitsPow_image_minus_image_inter
    {s : Set (InfinitePlace K → ℝ)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    mapToUnitsPow K '' s \ mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ { 0 } := by
  rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
  have hx'' : x ∉ s ∩ {x | 0 < x w₀} := fun h ↦ hx' (Set.mem_image_of_mem _ h)
  rw [Set.mem_singleton_iff, mapToUnitsPow_zero_iff']
  exact mapToUnitsPow_image_minus_image_inter_aux K hs ⟨hx, hx''⟩

theorem measurable_mapToUnitsPow_image {s : Set (InfinitePlace K → ℝ)}
    (hs : MeasurableSet s) (hs' : s ⊆ {x | 0 ≤ x w₀}) :
    MeasurableSet (mapToUnitsPow K '' s) := by
  have hm : MeasurableSet (mapToUnitsPow K '' (s ∩ {x | 0 < x w₀})) := by
    rw [PartialHomeomorph.image_eq_target_inter_inv_preimage _ (fun _ h ↦ h.2)]
    refine (mapToUnitsPow K).open_target.measurableSet.inter ?_
    have : MeasurableSet (s ∩ {x | 0 < x w₀}) :=
      hs.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
    exact MeasurableSet.preimage this (measurable_mapToUnitsPow_symm K)
  obtain h | h : mapToUnitsPow K '' s = mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ∨
      mapToUnitsPow K '' s = mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ∪ { 0 } := by
    have h₀ : mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ mapToUnitsPow K '' s :=
      Set.image_mono Set.inter_subset_left
    obtain h₁ | h₁ := Set.subset_singleton_iff_eq.mp (mapToUnitsPow_image_minus_image_inter K hs')
    · left
      rw [Set.eq_union_of_diff_subset h₀ h₁, Set.union_empty]
    · right
      rw [Set.eq_union_of_diff_subset h₀ h₁]
  · rwa [h]
  · rw [h]
    exact MeasurableSet.union hm (measurableSet_singleton 0)

open ContinuousLinearMap

abbrev mapToUnitsPow_fDeriv_single (c : InfinitePlace K → ℝ) (i w : InfinitePlace K) :
    (InfinitePlace K → ℝ) →L[ℝ] ℝ := by
  classical
  exact if hi : i = w₀ then proj w₀ else
    (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)) ^ c i *
      (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log) • proj i

theorem hasFDeriv_mapToUnitsPow_single (c : InfinitePlace K → ℝ) (i w : InfinitePlace K)
    (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (fun x ↦ mapToUnitsPow_single K x i w)
      (mapToUnitsPow_fDeriv_single K c i w) {x | 0 ≤ x w₀} c := by
  unfold mapToUnitsPow_single mapToUnitsPow_fDeriv_single
  split_ifs
  · refine HasFDerivWithinAt.congr' (hasFDerivWithinAt_apply w₀ c _) ?_ hc
    exact fun _ h ↦ by simp_rw [abs_of_nonneg (Set.mem_setOf.mp h)]
  · exact HasFDerivWithinAt.const_rpow (hasFDerivWithinAt_apply i c _) <| pos_iff.mpr (by aesop)

open Classical in
abbrev jacobianCoeff (w i : InfinitePlace K) : (InfinitePlace K → ℝ) → ℝ :=
  fun c ↦ if hi : i = w₀ then 1 else |c w₀| * (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log

abbrev jacobian (c : InfinitePlace K → ℝ) : (InfinitePlace K → ℝ) →L[ℝ] InfinitePlace K → ℝ :=
  pi fun i ↦ (mapToUnitsPow₀ K (fun w ↦ c w) i • ∑ w, (jacobianCoeff K i w c) • proj w)

theorem hasFDeriv_mapToUnitsPow (c : InfinitePlace K → ℝ) (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (mapToUnitsPow K) (jacobian K c) {x | 0 ≤ x w₀} c := by
  classical
  refine hasFDerivWithinAt_pi'.mpr fun w ↦ ?_
  simp_rw [mapToUnitsPow_eq_prod_single]
  convert HasFDerivWithinAt.finset_prod fun i _ ↦ hasFDeriv_mapToUnitsPow_single K c i w hc
  rw [ContinuousLinearMap.proj_pi, Finset.smul_sum]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  by_cases hi : i = w₀
  · simp_rw [hi, jacobianCoeff, dite_true, one_smul, dif_pos, mapToUnitsPow₀_eq_prod_single]
  · rw [mapToUnitsPow₀_eq_prod_single, jacobianCoeff, dif_neg hi, smul_smul, ← mul_assoc,
      show |c w₀| = mapToUnitsPow_single K c w₀ w by simp_rw [dif_pos rfl],
      Finset.prod_erase_mul _ _ (Finset.mem_univ w₀), mapToUnitsPow_fDeriv_single, dif_neg hi,
      smul_smul,  ← mul_assoc, show w (algebraMap (𝓞 K) K
        (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ c i = mapToUnitsPow_single K c i w by
      simp_rw [dif_neg hi], Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

open Classical in
theorem prod_mapToUnitsPow₀(c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    ∏ w : InfinitePlace K, mapToUnitsPow₀ K c w =
      (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K c w)⁻¹ := by
  have : ∏ w : { w  // IsComplex w}, (mapToUnitsPow₀ K) c w.val ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ ↦ ne_of_gt (mapToUnitsPow₀_pos K c w)
  rw [← mul_eq_one_iff_eq_inv₀ this]
  convert norm_mapToUnitsPow₀ K c
  simp_rw [norm_realToMixed, ← Fintype.prod_subtype_mul_prod_subtype (fun w ↦ IsReal w)]
  rw [← (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)).prod_comp]
  simp_rw [Equiv.subtypeEquivRight_apply_coe]
  rw [mul_assoc, ← sq, ← Finset.prod_pow]
  congr with w
  · rw [Real.norm_eq_abs, abs_of_pos (mapToUnitsPow₀_pos K c _), mult, if_pos w.prop, pow_one]
  · rw [Real.norm_eq_abs, abs_of_pos (mapToUnitsPow₀_pos K c _), mult, if_neg w.prop]

open Classical in
theorem jacobian_det {c : InfinitePlace K → ℝ} (hc : 0 ≤ c w₀) :
    |(jacobian K c).det| =
      (∏ w : {w : InfinitePlace K // w.IsComplex }, mapToUnitsPow₀ K (fun w ↦ c w) w)⁻¹ *
        2⁻¹ ^ NrComplexPlaces K * |c w₀| ^ (rank K) * (finrank ℚ K) * regulator K := by
  have : LinearMap.toMatrix' (jacobian K c).toLinearMap =
      Matrix.of fun w i ↦ mapToUnitsPow₀ K (fun w ↦ c w) w * jacobianCoeff K w i c := by
    ext
    simp_rw [jacobian, ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_smul,
      ContinuousLinearMap.coe_sum, LinearMap.toMatrix'_apply, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', this]
  rw [Matrix.det_mul_column, prod_mapToUnitsPow₀, ← Matrix.det_transpose]
  simp_rw [jacobianCoeff]
  rw [mul_assoc, finrank_mul_regulator_eq_det K w₀ equivFinRank.symm]
  have : |c w₀| ^ rank K = |∏ w : InfinitePlace K, if w = w₀ then 1 else c w₀| := by
    rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul, abs_pow]
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, rank]
  rw [this, mul_assoc, ← abs_mul, ← Matrix.det_mul_column]
  have : (2 : ℝ)⁻¹ ^ NrComplexPlaces K = |∏ w : InfinitePlace K, (mult w : ℝ)⁻¹| := by
    rw [Finset.abs_prod]
    simp_rw [mult, Nat.cast_ite, Nat.cast_one, Nat.cast_ofNat, apply_ite, abs_inv, abs_one, inv_one,
      Nat.abs_ofNat, Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
    rw [Finset.filter_not, Finset.card_univ_diff, ← Fintype.card_subtype]
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, ← NrRealPlaces, add_tsub_cancel_left]
  rw [this, mul_assoc, ← abs_mul, ← Matrix.det_mul_row, abs_mul]
  congr
  · rw [abs_eq_self.mpr]
    rw [inv_nonneg]
    exact Finset.prod_nonneg fun _ _ ↦ (mapToUnitsPow₀_pos K _ _).le
  · ext
    simp only [Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul, mul_ite]
    split_ifs
    · rw [inv_mul_cancel₀ mult_coe_ne_zero]
    · rw [← mul_assoc, mul_comm _ (c w₀), mul_assoc, inv_mul_cancel_left₀ mult_coe_ne_zero,
        abs_eq_self.mpr hc]

theorem setLIntegral_mapToUnitsPow_aux₀ {s : Set (InfinitePlace K → ℝ)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    s \ (s ∩ {x | 0 < x w₀}) ⊆ {x | x w₀ = 0} := by
  refine fun _ h ↦ eq_of_ge_of_not_gt (hs h.1) ?_
  have := h.2
  simp_rw [Set.mem_inter_iff, not_and, h.1, true_implies] at this
  exact this

theorem setLIntegral_mapToUnitsPow_aux₁ :
    volume {x : InfinitePlace K → ℝ | x w₀ = 0} = 0 := by
  let A : AffineSubspace ℝ (InfinitePlace K → ℝ) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w₀ = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  have : 1 ∈ A := h ▸ Set.mem_univ _
  simp [A] at this

theorem setLIntegral_mapToUnitsPow_aux₂ {s : Set (InfinitePlace K → ℝ)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    (mapToUnitsPow K) '' s =ᵐ[volume] (mapToUnitsPow K) '' (s ∩ {x | 0 < x w₀}) := by
  refine measure_symmDiff_eq_zero_iff.mp ?_
  rw [symmDiff_of_ge (Set.image_mono Set.inter_subset_left)]
  have : mapToUnitsPow K '' s \ mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ { 0 } := by
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    have hx'' : x ∉ s ∩ {x | 0 < x w₀} := fun h ↦ hx' (Set.mem_image_of_mem _ h)
    rw [Set.mem_singleton_iff, mapToUnitsPow_zero_iff']
    exact setLIntegral_mapToUnitsPow_aux₀ K hs ⟨hx, hx''⟩
  exact measure_mono_null this (measure_singleton _)

open ENNReal Classical in
theorem setLIntegral_mapToUnitsPow {s : Set (InfinitePlace K → ℝ)} (hs₀ : MeasurableSet s)
    (hs₁ : s ⊆ {x | 0 ≤ x w₀}) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (mapToUnitsPow K) '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * ENNReal.ofReal (regulator K) * (finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal |x w₀| ^ rank K *
        ENNReal.ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
          (mapToUnitsPow₀ K (fun w ↦ x w) i))⁻¹ * f (mapToUnitsPow K x) := by
  rw [setLIntegral_congr (setLIntegral_mapToUnitsPow_aux₂ K hs₁)]
  have : s =ᵐ[volume] (s ∩ {x | 0 < x w₀} : Set (InfinitePlace K → ℝ)) := by
    refine measure_symmDiff_eq_zero_iff.mp <|
      measure_mono_null ?_ (setLIntegral_mapToUnitsPow_aux₁ K)
    rw [symmDiff_of_ge Set.inter_subset_left]
    exact setLIntegral_mapToUnitsPow_aux₀ K hs₁
  rw [setLIntegral_congr this]
  have h : MeasurableSet (s ∩ {x | 0 < x w₀}) :=
    hs₀.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume h (fun c hc ↦
    HasFDerivWithinAt.mono (hasFDeriv_mapToUnitsPow K c (hs₁ (Set.mem_of_mem_inter_left hc)))
    (Set.inter_subset_left.trans hs₁)) ((mapToUnitsPow K).injOn.mono Set.inter_subset_right)]
  rw [setLIntegral_congr_fun h
    (ae_of_all volume fun c hc ↦ by rw [jacobian_det K (hs₁ (Set.mem_of_mem_inter_left hc))])]
  rw [← lintegral_const_mul']
  · congr with x
    have : 0 ≤ (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K (fun w ↦ x w) w)⁻¹ :=
      inv_nonneg.mpr <| Finset.prod_nonneg fun w _ ↦ (mapToUnitsPow₀_pos K _ w).le
    rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
      ofReal_mul (by positivity), ofReal_natCast, ofReal_pow (by positivity), ofReal_pow
      (by positivity), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat]
    ring
  · exact mul_ne_top (mul_ne_top (pow_ne_top (inv_ne_top.mpr two_ne_zero)) ofReal_ne_top)
      (natCast_ne_top _)

open Classical in
abbrev box₁ : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

theorem mem_Ioc_of_mem_box₁ {c : InfinitePlace K → ℝ} (hc : c ∈ box₁ K) :
    c w₀ ∈ Set.Ioc 0 1 := by
  have := hc w₀ (Set.mem_univ _)
  simp_rw [ite_true] at this
  exact this

theorem mem_Ico_of_mem_box₁ {c : InfinitePlace K → ℝ} (hc : c ∈ box₁ K) {w : InfinitePlace K}
    (hw : w ≠ w₀) :
    c w ∈ Set.Ico 0 1 := by
  have := hc w (Set.mem_univ _)
  simp_rw [if_neg hw] at this
  exact this

theorem mixedToReal_normLessThanOne_eq :
    mixedToReal '' (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) = mapToUnitsPow K '' (box₁ K) := by
  classical
  rw [normLessThanOne_eq_union_smul_normEqOne, Set.iUnion₂_inter, Set.image_iUnion₂]
  ext
  rw [Set.mem_iUnion₂, Set.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr, ⟨_, ⟨⟨x, hx, rfl⟩, hx₂⟩, rfl⟩⟩
    have : mixedToReal x ∈ mixedToReal '' (normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) := by
      have hx₃ : ∀ w, normAtPlace w (fun w ↦ |x.1 w|, x.2) = normAtPlace w x := by
        intro w
        obtain hw | hw := isReal_or_isComplex w
        · simp_rw [normAtPlace_apply_isReal hw, Real.norm_eq_abs, abs_abs]
        · simp_rw [normAtPlace_apply_isComplex hw]
      have hx₄ : ∀ w, 0 < x.1 w := by
        intro w
        simp_rw [Set.mem_setOf_eq, Prod.smul_fst, Pi.smul_apply, smul_eq_mul] at hx₂
        exact pos_of_mul_pos_right (hx₂ w) hr.1.le
      refine ⟨(fun w ↦ |x.1 w|, x.2), ⟨?_, ?_⟩, ?_⟩
      · exact mem_normEqOne_of_normAtPlace_eq K hx hx₃
      · intro w
        exact abs_pos_of_pos (hx₄ w)
      · ext w
        obtain hw | hw := isReal_or_isComplex w
        · simp_rw [mixedToReal_apply_of_isReal hw, abs_of_pos (hx₄ ⟨w, hw⟩)]
        · simp_rw [mixedToReal_apply_of_isComplex hw]
    rw [mixedToReal_normEqOne_eq] at this
    obtain ⟨c, hc₁, hc₂⟩ := this
    refine ⟨?_, ?_, ?_⟩
    · exact fun w ↦ if hw : w = w₀ then r else c ⟨w, hw⟩
    · intro w _
      by_cases hw : w = w₀
      · simp_rw [hw, dite_true, if_true]
        exact hr
      · simp_rw [dif_neg hw, if_neg hw]
        exact hc₁ _ (Set.mem_univ _)
    · simp_rw [mapToUnitsPow_apply, dite_true, Subtype.coe_eta]
      conv_lhs =>
        enter [2, 2, w]
        rw [dif_neg w.prop]
      rw [hc₂, abs_of_nonneg hr.1.le, mixedToReal_smul _ hr.1.le]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c w₀, mem_Ioc_of_mem_box₁ K hc, ⟨?_, ⟨?_, ?_⟩, ?_⟩⟩
    · exact realToMixed (mapToUnitsPow K c)
    · rw [smul_normEqOne K (mem_Ioc_of_mem_box₁ K hc).1]
      refine ⟨?_, ?_⟩
      · rw [mapToUnitsPow_apply, _root_.map_smul, smul_mem_iff_mem,
          realToMixed_mapToUnitsPow₀_mem_fundamentalCone_iff]
        · exact fun i ↦ mem_Ico_of_mem_box₁ K hc i.prop
        · rw [abs_ne_zero]
          exact (mem_Ioc_of_mem_box₁ K hc).1.ne.symm
      · rw [mapToUnitsPow_apply, _root_.map_smul, mixedEmbedding.norm_smul, norm_mapToUnitsPow₀,
          mul_one, abs_of_pos, abs_of_pos]
        · exact (mem_Ioc_of_mem_box₁ K hc).1
        · refine abs_pos_of_pos (mem_Ioc_of_mem_box₁ K hc).1
    · intro w
      rw [realToMixed_apply_of_isReal]
      refine mapToUnitsPow_pos K ?_ _
      exact (mem_Ioc_of_mem_box₁ K hc).1.ne.symm
    · refine realToMixedToReal_eq_self_of_nonneg ?_
      intro w _
      refine (mapToUnitsPow_pos K ?_ _).le
      exact (mem_Ioc_of_mem_box₁ K hc).1.ne.symm

-- theorem vectorNormAtPlace_normLessThanOne_eq_image :
--     vectorNormAtPlace '' (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) =
--       mapToUnitsPow K '' (box₁ K) := by
--   classical
--   rw [normLessThanOne_eq_union_smul_normEqOne, Set.iUnion₂_inter, Set.image_iUnion₂]
--   ext
--   rw [Set.mem_iUnion₂, Set.mem_image]
--   refine ⟨?_, ?_⟩
--   · rintro ⟨r, hr, ⟨_, ⟨⟨x, hx, rfl⟩, hx₂⟩, rfl⟩⟩
--     have : vectorNormAtPlace x ∈ vectorNormAtPlace '' (normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) := by
--       have hn : ∀ w, normAtPlace w (fun w ↦ |x.1 w|, x.2) = normAtPlace w x := by
--         intro w
--         obtain hw | hw := isReal_or_isComplex w
--         · simp_rw [normAtPlace_apply_isReal hw, Real.norm_eq_abs, abs_abs]
--         · simp_rw [normAtPlace_apply_isComplex hw]
--       refine ⟨(fun w ↦ |x.1 w|, x.2), ⟨?_, ?_⟩, ?_⟩
--       · exact mem_normEqOne_of_normAtPlace_eq K hx hn
--       · intro w
--         dsimp only
--         rw [← Real.norm_eq_abs, ← normAtPlace_apply_isReal]
--         exact normAtPlace_pos_of_mem hx.1 w
--       · ext w
--         rw [vectorNormAtPlace, vectorNormAtPlace, hn]
--     rw [vectorNormAtPlace_normEqOne_eq_image] at this
--     obtain ⟨c, hc₁, hc₂⟩ := this
--     refine ⟨?_, ?_, ?_⟩
--     · exact fun w ↦ if hw : w = w₀ then r else c ⟨w, hw⟩
--     · -- simp_rw [Set.mem_pi, Set.mem_univ, true_implies]
--       intro w _
--       by_cases hw : w = w₀
--       · simp_rw [hw, dite_true, if_true]
--         exact hr
--       · simp_rw [dif_neg hw, if_neg hw]
--         exact hc₁ _ (Set.mem_univ _)
--     · simp_rw [mapToUnitsPow_apply, dite_true, Subtype.coe_eta]
--       conv_lhs =>
--         enter [2, 2, w]
--         rw [dif_neg w.prop]
--       rw [hc₂, abs_of_nonneg hr.1.le, vectorNormAtPlace_smul _ hr.1.le]
--   · rintro ⟨c, hc, rfl⟩
--     refine ⟨c w₀, mem_Ioc_of_mem_box₁ K hc, ⟨?_, ⟨?_, ?_⟩, ?_⟩⟩
--     · exact realToMixed (mapToUnitsPow K c)
--     · rw [smul_normEqOne K (mem_Ioc_of_mem_box₁ K hc).1]
--       refine ⟨?_, ?_⟩
--       · rw [mapToUnitsPow_apply, _root_.map_smul, smul_mem_iff_mem,
--           realToMixed_mapToUnitsPow₀_mem_fundamentalCone_iff]
--         · exact fun i ↦ mem_Ico_of_mem_box₁ K hc i.prop
--         · rw [abs_ne_zero]
--           exact (mem_Ioc_of_mem_box₁ K hc).1.ne.symm
--       · rw [mapToUnitsPow_apply, _root_.map_smul, mixedEmbedding.norm_smul, norm_mapToUnitsPow₀,
--           mul_one, abs_of_pos, abs_of_pos]
--         · exact (mem_Ioc_of_mem_box₁ K hc).1
--         · refine abs_pos_of_pos (mem_Ioc_of_mem_box₁ K hc).1
--     · intro w
--       rw [realToMixed_apply_of_isReal]
--       refine mapToUnitsPow_pos K ?_ _
--       exact (mem_Ioc_of_mem_box₁ K hc).1.ne.symm
--     · rw [vectorNormAtPlace_realToMixed_of_nonneg]
--       exact fun _ ↦ (mapToUnitsPow_pos K (mem_Ioc_of_mem_box₁ K hc).1.ne.symm _).le

open Classical in
def realProdComplexProdMeasurableEquiv :
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ) ≃ᵐ
       (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  MeasurableEquiv.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans MeasurableEquiv.prodAssoc.symm <|
       MeasurableEquiv.trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.arrowCongr'
          (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm))
        (MeasurableEquiv.refl _))) (MeasurableEquiv.refl _))
        (MeasurableEquiv.prodCongr (MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm
        (MeasurableEquiv.refl _))

open Classical in
-- marcus₂.symm
def realProdComplexProdEquiv :
    ({w : InfinitePlace K // IsReal w} → ℝ) ×
      ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ) ≃ₜ
        (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ) where
  __ := realProdComplexProdMeasurableEquiv K
  continuous_toFun := by
    change Continuous fun x ↦ ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    by_cases hw : IsReal w
    · simp_rw [dif_pos hw]; fun_prop
    · simp_rw [dif_neg hw]; fun_prop
  continuous_invFun := by
    change Continuous fun x ↦ (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩)
    fun_prop

open Classical in
theorem volume_preserving_realProdComplexProdEquiv :
    MeasurePreserving (realProdComplexProdEquiv K) := by
  change MeasurePreserving (realProdComplexProdMeasurableEquiv K) volume volume
  exact MeasurePreserving.trans ((MeasurePreserving.id volume).prod
      (volume_preserving.arrowProdEquivProdArrow ℝ ℝ {w : InfinitePlace K // IsComplex w})) <|
    MeasurePreserving.trans (volume_preserving.prodAssoc.symm) <|
      MeasurePreserving.trans
        (((MeasurePreserving.id volume).prod (volume_preserving.arrowCongr' _
        (MeasurableEquiv.refl ℝ)
          (MeasurePreserving.id volume))).prod (MeasurePreserving.id volume))
      <| ((volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
        (fun w : InfinitePlace K ↦ IsReal w)).symm).prod (MeasurePreserving.id volume)

open Classical in
theorem realProdComplexProdEquiv_apply (x : ({w : InfinitePlace K // IsReal w} → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)) :
    realProdComplexProdEquiv K x = ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

theorem realProdComplexProdEquiv_symm_apply (x : (InfinitePlace K → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    (realProdComplexProdEquiv K).symm x = (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩) := rfl

def polarCoordMixedSpace : PartialHomeomorph
    (E K) ((InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  ((PartialHomeomorph.refl _).prod
    (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)).transHomeomorph (realProdComplexProdEquiv K)

theorem polarCoordMixedSpace_symm_apply (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    (polarCoordMixedSpace K).symm x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := rfl

theorem polarCoordMixedSpace_apply (x : E K) :
    polarCoordMixedSpace K x =
      (realProdComplexProdEquiv K) (x.1, fun w ↦ Complex.polarCoord (x.2 w)) := by
  rw [polarCoordMixedSpace]
  simp_rw [PartialHomeomorph.transHomeomorph_apply, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Function.comp_apply]
  rfl

theorem continuous_polarCoordMixedSpace_symm :
    Continuous (polarCoordMixedSpace K).symm := by
  change Continuous (fun x ↦ (polarCoordMixedSpace K).symm x)
  simp_rw [polarCoordMixedSpace_symm_apply]
  rw [continuous_prod_mk]
  refine ⟨?_, ?_⟩
  · fun_prop
  · rw [continuous_pi_iff]
    intro i
    refine Continuous.comp' ?_ ?_
    · exact Complex.continuous_polarCoord_symm
    · fun_prop

-- example :
--     Set.InjOn ((polarCoordMixedSpace K).symm)
--       ((Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ico (-π) π)) := by
--   intro x hx y hy hxy
--   simp_rw [polarCoordMixedSpace_symm_apply] at hxy
--   ext w
--   · obtain hw | hw := isReal_or_isComplex w
--     · exact congr_fun (congr_arg Prod.fst hxy) ⟨w, hw⟩
--     ·
--       sorry
--   · sorry

-- example {s t} (hs : MeasurableSet s) (ht : MeasurableSet t) :
--     MeasurableSet ((polarCoordMixedSpace K).symm '' s ×ˢ t) := by
--   dsimp [polarCoordMixedSpace]
--   simp

--   refine MeasurableSet.prod ?_ ?_
--   refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ ?_
--   · refine MeasurableSet.prod hs ht
--   · exact (continuous_polarCoordMixedSpace_symm K).continuousOn
--   ·
--     sorry

theorem polarCoordMixedSpace_source :
    (polarCoordMixedSpace K).source = Set.univ ×ˢ Set.univ.pi fun _ ↦ Complex.slitPlane := by
  simp [polarCoordMixedSpace, Complex.polarCoord_source]

open Classical in
theorem polarCoordMixedSpace_target : (polarCoordMixedSpace K).target =
  (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [polarCoordMixedSpace, PartialHomeomorph.transHomeomorph_target]
  ext
  simp_rw [Set.mem_preimage, realProdComplexProdEquiv_symm_apply, PartialHomeomorph.prod_target,
    Set.mem_prod, PartialHomeomorph.refl_target, PartialHomeomorph.pi_target,
    Complex.polarCoord_target]
  aesop

-- Simplify the proof of similar results in the same way
theorem measurableSet_polarCoordMixedSpace_target :
    MeasurableSet (polarCoordMixedSpace K).target :=
  IsOpen.measurableSet (polarCoordMixedSpace K).open_target

theorem realProdComplexProdEquiv_preimage_polarCoordMixedSpace_target :
  (realProdComplexProdEquiv K) ⁻¹' (polarCoordMixedSpace K).target =
    Set.univ ×ˢ Set.univ.pi fun _ ↦ polarCoord.target := by
  ext
  simp_rw [polarCoordMixedSpace_target, Set.mem_preimage, realProdComplexProdEquiv_apply,
    polarCoord_target, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, true_and,
    Set.mem_ite_univ_left, not_isReal_iff_isComplex, Set.mem_prod]
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩ i
    refine ⟨?_, ?_⟩
    · specialize h₁ i i.prop
      rwa [dif_neg] at h₁
      rw [not_isReal_iff_isComplex]
      exact i.prop
    · specialize h₂ i
      exact h₂
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [dif_neg]
      specialize h ⟨i, hi⟩
      exact h.1
      rwa [not_isReal_iff_isComplex]
    · intro i
      specialize h i
      exact h.2

open Classical in
theorem lintegral_mixedSpace_eq (f : (E K) → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x =
      ∫⁻ x in (polarCoordMixedSpace K).target,
        (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal) *
          f ((polarCoordMixedSpace K).symm x) := by
  have h : Measurable fun x ↦ (∏ w : { w // IsComplex w}, (x.1 w.val).toNNReal) *
      f ((polarCoordMixedSpace K).symm x) := by
    refine Measurable.mul ?_ ?_
    · exact measurable_coe_nnreal_ennreal_iff.mpr <| Finset.measurable_prod _ fun _ _ ↦ by fun_prop
    · exact hf.comp' (continuous_polarCoordMixedSpace_symm K).measurable
  rw [← (volume_preserving_realProdComplexProdEquiv K).setLIntegral_comp_preimage
    (measurableSet_polarCoordMixedSpace_target K) h, volume_eq_prod, volume_eq_prod,
    lintegral_prod _ hf.aemeasurable]
  simp_rw [Complex.lintegral_pi_comp_polarCoord_symm _ (hf.comp' measurable_prod_mk_left)]
  rw [realProdComplexProdEquiv_preimage_polarCoordMixedSpace_target,
    ← Measure.restrict_prod_eq_univ_prod, lintegral_prod _
    (h.comp' (realProdComplexProdEquiv K).measurable).aemeasurable]
  simp_rw [realProdComplexProdEquiv_apply, polarCoordMixedSpace_symm_apply,
    dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]

def mapToUnitsPowComplex : PartialHomeomorph
    ((InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) (E K) :=
  PartialHomeomorph.trans
    (PartialHomeomorph.prod (mapToUnitsPow K) (PartialHomeomorph.refl _))
    (polarCoordMixedSpace K).symm

theorem mapToUnitsPowComplex_apply (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    mapToUnitsPowComplex K x =
      (fun w ↦ mapToUnitsPow K x.1 w.val,
        fun w ↦ Complex.polarCoord.symm (mapToUnitsPow K x.1 w.val, x.2 w)) := rfl

theorem mapToUnitsPowComplex_source :
    (mapToUnitsPowComplex K).source = {x | 0 < x w₀} ×ˢ Set.univ.pi fun _ ↦ Set.Ioo (-π) π := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.trans_source, PartialHomeomorph.prod_source,
    PartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
    Set.mem_preimage, PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq,
    PartialHomeomorph.symm_source, polarCoordMixedSpace_target, Set.mem_prod, mapToUnitsPow_source]
  rw [and_congr_right]
  intro h
  rw [and_iff_right_iff_imp]
  intro _
  simp_rw [Set.mem_univ_pi, Set.mem_ite_univ_left, not_isReal_iff_isComplex]
  intro w _
  rw [Set.mem_Ioi, lt_iff_le_and_ne]
  refine ⟨mapToUnitsPow_nonneg K _ _, ?_⟩
  rw [ne_comm, ne_eq, mapToUnitsPow_zero_iff]
  exact ne_of_gt h

theorem mapToUnitsPowComplex_target :
    (mapToUnitsPowComplex K).target =
      (Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Complex.slitPlane) := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.trans_target, PartialHomeomorph.symm_target,
    polarCoordMixedSpace_source, PartialHomeomorph.prod_target, PartialHomeomorph.refl_target,
    Set.mem_inter_iff, Set.mem_preimage, mapToUnitsPow_target, Set.mem_prod, Set.mem_univ,
    true_and, and_true, and_comm]
  rw [and_congr_right]
  intro h
  simp_rw [PartialHomeomorph.symm_symm, polarCoordMixedSpace_apply, realProdComplexProdEquiv_apply,
    Set.mem_pi, Set.mem_univ, true_implies]
  refine ⟨?_, ?_⟩
  · intro h' w
    specialize h' w
    simp_rw [dif_pos w.prop] at h'
    exact h'
  · intro h' w
    by_cases hw : IsReal w
    · simp_rw [dif_pos hw]
      exact h' ⟨w, hw⟩
    · simp_rw [dif_neg hw]
      rw [Complex.polarCoord_apply]
      dsimp only
      rw [Set.mem_pi] at h
      specialize h ⟨w, not_isReal_iff_isComplex.mp hw⟩ (Set.mem_univ _)
      rw [AbsoluteValue.pos_iff]
      exact Complex.slitPlane_ne_zero h

theorem continuous_mapToUnitsPowComplex :
    Continuous (mapToUnitsPowComplex K) := by
  simp [mapToUnitsPowComplex]
  refine Continuous.comp ?_ ?_
  · exact continuous_polarCoordMixedSpace_symm K
  · rw [continuous_prod_mk]
    refine ⟨?_, ?_⟩
    · exact (continuous_mapToUnitsPow K).comp' continuous_fst
    · exact continuous_snd

theorem mapToUnitsPowComplex_image_prod (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    mapToUnitsPowComplex K '' (s ×ˢ t) =
      (polarCoordMixedSpace K).symm '' (mapToUnitsPow K '' s) ×ˢ t := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.coe_trans, Function.comp_apply,
    PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq,
    polarCoordMixedSpace_symm_apply, Set.mem_image, Set.mem_prod, Prod.exists]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨mapToUnitsPow K x, y, ⟨Set.mem_image_of_mem _ hx, hy⟩, rfl⟩
  · rintro ⟨_, y, ⟨⟨⟨x, hx, rfl⟩, hy⟩, rfl⟩⟩
    exact ⟨x, y, ⟨hx, hy⟩, rfl⟩

theorem _root_.Complex.polarCoord_symm_mem_slitPlane (x : ℝ × ℝ) :
    Complex.polarCoord.symm x ∈ Complex.polarCoord.source ↔
        x.1 ≠ 0 ∧ (x.1 > 0 → ∀ k : ℤ, π + k * (2 * π) ≠ x.2) ∧
          (x.1 < 0 →  ∀ k : ℤ, k * (2 * π) ≠ x.2) := by
  rw [← not_iff_not]
  simp_rw [Complex.polarCoord_source, Complex.mem_slitPlane_iff, Complex.polarCoord_symm_apply,
    Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos_add_sin_I, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.im_ofReal_mul, ne_eq, mul_eq_zero,
    Complex.exp_ofReal_mul_I_im, mul_pos_iff,
    Real.sin_eq_zero_iff_cos_eq, not_and_or, not_or, not_and_or, _root_.not_imp, not_forall,
    not_not]
  obtain hx | hx | hx := lt_trichotomy x.1 0
  · simp_rw [hx, not_lt_of_gt hx, ne_of_lt hx, not_false_eq_true, not_true_eq_false, true_or,
      true_and, false_or, false_and, false_or, and_or_left]
    rw [or_iff_left, and_iff_right_of_imp, Real.cos_eq_one_iff]
    · intro h
      rw [h]
      linarith
    · refine not_and'.mpr ?_
      intro h
      rw [h, not_not]
      linarith
  · simp_rw [hx, lt_self_iff_false, not_false_eq_true, true_or, true_and]
  · simp_rw [hx, not_lt_of_gt hx, ne_of_gt hx, not_false_eq_true, not_true_eq_false, true_or,
      and_true, true_and, false_or, false_and, or_false, and_or_left]
    rw [or_iff_right, and_iff_right_of_imp, Real.cos_eq_neg_one_iff]
    · intro h
      rw [h]
      linarith
    · refine not_and'.mpr ?_
      intro h
      rw [h, not_not]
      exact zero_lt_one

theorem mapToUnitsPowComplex_prod_indicator_aux (x y : ℝ × ℝ) (hx : x ∈ Set.Ici 0 ×ˢ Set.Icc (-π) π)
    (hy : y ∈ Complex.polarCoord.target)
    (hxy : Complex.polarCoord.symm x = Complex.polarCoord.symm y) :
    x = y := by
  suffices x ∈ Complex.polarCoord.target from Complex.polarCoord.symm.injOn this hy hxy
  suffices x.1 ≠ 0 ∧ x.2 ≠ -π ∧ x.2 ≠ π by
    simp only [Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    simp at hx
    refine ⟨?_, ?_, ?_⟩
    · rw [lt_iff_le_and_ne]
      exact ⟨hx.1, this.1.symm⟩
    · rw [lt_iff_le_and_ne]
      exact ⟨hx.2.1, this.2.1.symm⟩
    · rw [lt_iff_le_and_ne]
      exact ⟨hx.2.2, this.2.2⟩
  have := (Complex.polarCoord_symm_mem_slitPlane x).mp ?_
  have hx₁ : 0 < x.1 := by
    refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
    exact hx.1
    exact this.1.symm
  · refine ⟨?_, ?_, ?_⟩
    · exact this.1
    · have := this.2.1 hx₁ (-1)
      rwa [show π + (-1 : ℤ) * (2 * π) = -π by ring, ne_comm] at this
    · have := this.2.1 hx₁ 0
      rwa [Int.cast_zero, zero_mul, add_zero, ne_comm] at this
  · rw [hxy]
    exact Complex.polarCoord.map_target hy

theorem mapToUnitsPowComplex_prod_indicator
    {s : Set (InfinitePlace K → ℝ)} {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)}
    (ht : t ⊆ Set.univ.pi fun _ ↦ Set.Icc (-π) π)
    (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ))
    (hx : x ∈ (polarCoordMixedSpace K).target) :
    (mapToUnitsPowComplex K '' s ×ˢ t).indicator (fun _ ↦ (1 : ENNReal))
      ((polarCoordMixedSpace K).symm x) =
      (mapToUnitsPow K '' s).indicator 1 x.1 * t.indicator 1 x.2 := by
  classical
  simp_rw [mapToUnitsPowComplex_image_prod, ← Set.indicator_prod_one, Prod.mk.eta,
    Set.indicator_apply, Set.mem_image, polarCoordMixedSpace_symm_apply, Prod.mk.inj_iff]
  refine if_congr ⟨fun ⟨y, hy, ⟨hxy₁, hxy₂⟩⟩ ↦ ?_, fun h ↦ ⟨x, h, rfl, rfl⟩⟩ rfl rfl
  suffices y = x by rwa [← this]
  have hxy : ∀ i (hi : IsComplex i), y.1 i = x.1 i ∧ y.2 ⟨i, hi⟩ = x.2 ⟨i, hi⟩ := by
      intro i hi
      rw [← Prod.mk.inj_iff]
      refine mapToUnitsPowComplex_prod_indicator_aux _ _ ?_ ?_ (congr_fun hxy₂ ⟨i, hi⟩)
      · rw [Set.prod_mk_mem_set_prod_eq]
        refine ⟨?_, ?_⟩
        · obtain ⟨t, _, ht⟩ := hy.1
          rw [← ht]
          exact mapToUnitsPow_nonneg _ _ _
        · exact ht hy.2 ⟨i, hi⟩ trivial
      · simp_rw [polarCoordMixedSpace_target, Set.mem_prod, Set.mem_univ_pi, Set.mem_ite_univ_left,
          not_isReal_iff_isComplex] at hx
        exact ⟨hx.1 i hi, hx.2 ⟨i, hi⟩⟩
  ext i
  · obtain hi | hi := isReal_or_isComplex i
    · exact congr_fun hxy₁ ⟨i, hi⟩
    · exact (hxy i hi).1
  · exact (hxy i.val i.prop).2

open Classical in
theorem volume_mapToUnitsPowComplex_set_prod_set {s : Set (InfinitePlace K → ℝ)}
    (hs : MeasurableSet s) (hs' : s ⊆ {x | 0 ≤ x w₀} )
    {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)}
    (ht : MeasurableSet t) (ht' : t ⊆ Set.univ.pi fun _ ↦ Set.Icc (-π) π)
    (hm : MeasurableSet (mapToUnitsPowComplex K '' s ×ˢ t)) :
    volume (mapToUnitsPowComplex K '' (s ×ˢ t)) =
      volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) * ∫⁻ x in mapToUnitsPow K '' s,
        ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator _ hm, lintegral_mixedSpace_eq K _
    ((measurable_indicator_const_iff 1).mpr hm),
    setLIntegral_congr (setLIntegral_mapToUnitsPow_aux₂ K hs')]
  calc
    _ = ∫⁻ x in Set.univ.pi fun w ↦ if IsReal w then Set.univ else Set.Ioi 0,
          ∫⁻ y in Set.univ.pi fun _ ↦ Set.Ioo (-π) π,
            (∏ w : {w // IsComplex w}, (x w.val).toNNReal) *
              ((mapToUnitsPow K '' s).indicator 1 x * t.indicator 1 y) := by
      rw [lintegral_lintegral, Measure.prod_restrict, ← polarCoordMixedSpace_target]
      · refine setLIntegral_congr_fun (measurableSet_polarCoordMixedSpace_target K) ?_
        filter_upwards with x hx
        simp_rw [mapToUnitsPowComplex_prod_indicator K ht' x hx]
      · refine Measurable.aemeasurable ?_
        refine Measurable.mul ?_ ?_
        · exact measurable_coe_nnreal_ennreal_iff.mpr <|
            Finset.measurable_prod _ fun _ _ ↦ by fun_prop
        · refine Measurable.mul ?_ ?_
          · refine Measurable.ite ?_ ?_ ?_
            · change MeasurableSet (Prod.fst ⁻¹' (mapToUnitsPow K '' s))
              refine measurable_fst ?_
              refine measurable_mapToUnitsPow_image K hs hs'
            · exact measurable_const
            · exact measurable_const
          · refine Measurable.comp' ?_ measurable_snd
            exact measurable_const.indicator ht
    _ = volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) *
          ∫⁻ x in Set.univ.pi fun w ↦ if IsReal w then Set.univ else Set.Ioi 0,
            (∏ w : {w // IsComplex w}, (x w.val).toNNReal) *
              (mapToUnitsPow K '' s).indicator 1 x := by
      conv_lhs =>
        enter [2, x]
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        rw [lintegral_const_mul' _ _ (by
            rw [Set.indicator_apply]
            split_ifs
            exacts [ENNReal.one_ne_top, ENNReal.zero_ne_top])]
        rw [← lintegral_indicator _ (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo),
          Set.indicator_indicator, lintegral_indicator_one ((MeasurableSet.univ_pi
          fun _ ↦ measurableSet_Ioo).inter ht)]
      rw [← lintegral_const_mul']
      · congr with x
        ring
      · refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
        simp_rw [volume_pi, pi_pi, Real.volume_Ioo, Finset.prod_const]
        refine ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    _ = volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) *
          ∫⁻ x in Set.univ.pi fun w ↦ if IsReal w then Set.univ else Set.Ioi 0,
            (∏ w : {w // IsComplex w}, (x w.val).toNNReal) *
              (mapToUnitsPow K '' (s ∩ {x | 0 < x w₀})).indicator 1 x := by
      congr 1
      refine lintegral_congr_ae ?_
      refine Filter.EventuallyEq.mul ?_ ?_
      · exact Filter.EventuallyEq.rfl
      · refine indicator_ae_eq_of_ae_eq_set ?_
        refine Filter.EventuallyEq.restrict ?_
        exact setLIntegral_mapToUnitsPow_aux₂ K hs'
    _ = volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) *
          ∫⁻ x in mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}),
            ∏ w : {w // IsComplex w}, (x w.val).toNNReal := by
      rw [← lintegral_indicator, ← lintegral_indicator]
      congr with x
      rw [Set.indicator_mul_right, Set.indicator_indicator, Set.inter_eq_right.mpr]
      by_cases hx : x ∈ (mapToUnitsPow K) '' (s ∩ {x | 0 < x w₀})
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one,
          ENNReal.coe_finset_prod]
      · rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem hx, mul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        refine Set.mem_univ_pi.mpr fun _ ↦ ?_
        rw [Set.mem_ite_univ_left]
        intro _
        rw [Set.mem_Ioi]
        refine mapToUnitsPow_pos K (ne_of_gt hx.2) _
      · refine measurable_mapToUnitsPow_image K ?_ ?_
        · exact hs.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
        · exact Set.inter_subset_left.trans hs'
      · refine MeasurableSet.univ_pi fun _ ↦ ?_
        refine MeasurableSet.ite' (fun _ ↦ ?_) (fun _ ↦ ?_)
        exact MeasurableSet.univ
        exact measurableSet_Ioi

abbrev box₂ : Set ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioc (-π) π

abbrev box := (box₁ K) ×ˢ (box₂ K)

theorem measurableSet_box₁ :
    MeasurableSet (box₁ K) :=
  MeasurableSet.univ_pi fun _ ↦
    MeasurableSet.ite' (fun _ ↦ measurableSet_Ioc) (fun _ ↦ measurableSet_Ico)

theorem measurableSet_box₂ :
    MeasurableSet (box₂ K) := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

theorem measurableSet_box :
    MeasurableSet (box K) := MeasurableSet.prod (measurableSet_box₁ K) (measurableSet_box₂ K)

abbrev normLessThanOnePlus : (Set (E K)) := plusPart (normLessThanOne K)

theorem normLessThanOnePlus_measurableSet :
    MeasurableSet (normLessThanOnePlus K) :=
  measurableSet_plusPart _ (measurableSet_normLessThanOne K)

theorem mixedToReal_mapToUnitsPowComplex
    (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    mixedToReal (mapToUnitsPowComplex K x) = mapToUnitsPow K x.1 := by
  ext w
  simp_rw [mapToUnitsPowComplex_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal hw]
  · rw [mixedToReal_apply_of_isComplex hw, Complex.norm_eq_abs, Complex.polarCoord_symm_abs,
      abs_of_nonneg (mapToUnitsPow_nonneg K x.1 w)]

-- theorem vectorNormAtPlace_mapToUnitsPowComplex
--     (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
--     vectorNormAtPlace (mapToUnitsPowComplex K x) = mapToUnitsPow K x.1 := by
--   ext w
--   simp_rw [mapToUnitsPowComplex_apply, vectorNormAtPlace]
--   obtain hw | hw := isReal_or_isComplex w
--   · rw [normAtPlace_apply_isReal hw, Real.norm_eq_abs, abs_of_nonneg (mapToUnitsPow_nonneg K x.1 _)]
--   · rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.polarCoord_symm_abs,
--       abs_of_nonneg (mapToUnitsPow_nonneg K x.1 w)]

theorem toto (A : Set (E K)) (t : Set (InfinitePlace K → ℝ))
    (hA₁ : ∀ x, x ∈ A ↔ mixedToReal x ∈ mixedToReal '' A)
    (hA₂ : mixedToReal '' A = mapToUnitsPow K '' t)
    (hA₃ : A ⊆ {x | ∀ w, 0 ≤ x.1 w}) :
    mapToUnitsPowComplex K '' (t ×ˢ (box₂ K)) = A := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    rw [hA₁, mixedToReal_mapToUnitsPowComplex]
    refine ⟨mapToUnitsPowComplex K y, ?_, ?_⟩
    · rw [hA₁, hA₂, mixedToReal_mapToUnitsPowComplex]
      refine ⟨y.1, hy.1, rfl⟩
    · exact mixedToReal_mapToUnitsPowComplex K y
  · intro h
    have hx : ∀ w, 0 ≤ x.1 w := fun w ↦ hA₃ h w
    rw [hA₁, hA₂] at h
    obtain ⟨c, hc₁, hc₂⟩ := h
    refine ⟨⟨c, ?_⟩, ⟨hc₁, ?_⟩, ?_⟩
    · exact fun w ↦ (x.2 w).arg
    · rw [Set.mem_univ_pi]
      intro w
      exact Complex.arg_mem_Ioc (x.2 w)
    · ext w
      · simp_rw [mapToUnitsPowComplex_apply, hc₂, mixedToReal_apply_of_isReal w.prop]
      · simp_rw [mapToUnitsPowComplex_apply, Complex.polarCoord_symm_apply, hc₂,
          mixedToReal_apply_of_isComplex w.prop, Complex.norm_eq_abs, Complex.ofReal_cos,
          Complex.ofReal_sin, Complex.abs_mul_cos_add_sin_mul_I]

-- theorem toto (A : Set (E K)) (t : Set (InfinitePlace K → ℝ))
--     (hA₁ : ∀ x, x ∈ A ↔ vectorNormAtPlace x ∈ vectorNormAtPlace '' A)
--     (hA₂ : vectorNormAtPlace '' A = mapToUnitsPow K '' t)
--     (hA₃ : A ⊆ {x | ∀ w, 0 ≤ x.1 w}) :
--     mapToUnitsPowComplex K '' (t ×ˢ (box₂ K)) = A := by
--   ext x
--   refine ⟨?_, ?_⟩
--   · rintro ⟨y, hy, rfl⟩
--     rw [hA₁, vectorNormAtPlace_mapToUnitsPowComplex]
--     refine ⟨mapToUnitsPowComplex K y, ?_, ?_⟩
--     · rw [hA₁, hA₂, vectorNormAtPlace_mapToUnitsPowComplex]
--       refine ⟨y.1, hy.1, rfl⟩
--     · exact vectorNormAtPlace_mapToUnitsPowComplex K y
--   · intro h
--     have hx : ∀ w, 0 ≤ x.1 w := fun w ↦ hA₃ h w
--     rw [hA₁, hA₂] at h
--     obtain ⟨c, hc₁, hc₂⟩ := h
--     refine ⟨⟨c, ?_⟩, ⟨hc₁, ?_⟩, ?_⟩
--     · exact fun w ↦ (x.2 w).arg
--     · rw [Set.mem_univ_pi]
--       intro w
--       exact Complex.arg_mem_Ioc (x.2 w)
--     · ext w
--       · simp_rw [mapToUnitsPowComplex_apply, hc₂, vectorNormAtPlace, normAtPlace_apply_isReal
--           w.prop, Real.norm_eq_abs, abs_of_nonneg (hx _)]
--       · simp_rw [mapToUnitsPowComplex_apply, Complex.polarCoord_symm_apply, hc₂, vectorNormAtPlace,
--           normAtPlace_apply_isComplex w.prop, Complex.norm_eq_abs, Complex.ofReal_cos,
--           Complex.ofReal_sin, Complex.abs_mul_cos_add_sin_mul_I]

theorem normLessThanOnePlus_eq_image :
    normLessThanOnePlus K = mapToUnitsPowComplex K '' (box K) := by
  refine (toto _ _ _ ?_ ?_ ?_).symm
  · intro x
    refine ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ ↦ ⟨?_, ?_⟩⟩
    · refine mem_normLessThanOne_of_normAtPlace_eq hy.1 fun w ↦ ?_
      rw [← norm_mixedToReal, ← norm_mixedToReal, hyx]
    · intro w
      rw [← mixedToReal_apply_of_isReal w.prop, ← hyx, mixedToReal_apply_of_isReal w.prop]
      exact hy.2 w
  · exact mixedToReal_normLessThanOne_eq K
  · exact fun _ h w ↦ (h.2 w).le

theorem pos_of_mem_box₁ {x : InfinitePlace K → ℝ}  (hx : x ∈ box₁ K) :
    0 < x w₀ := by
  have := hx w₀ (Set.mem_univ w₀)
  simp_rw [if_true] at this
  exact this.1

theorem isBounded_box₁ : Bornology.IsBounded (box₁ K) := by
  refine Bornology.IsBounded.pi ?_
  intro i
  by_cases hi : i = w₀
  · rw [hi, if_pos rfl]
    exact Metric.isBounded_Ioc 0 1
  · rw [if_neg hi]
    exact Metric.isBounded_Ico 0 1

theorem isBounded_box₂ : Bornology.IsBounded (box₂ K) := by
  refine Bornology.IsBounded.pi ?_
  intro _
  exact Metric.isBounded_Ioc _ _

theorem closure_box₁ :
    closure (box₁ K) = Set.Icc 0 1 := by
  rw [closure_pi_set]
  simp_rw [← Set.pi_univ_Icc, Pi.zero_apply, Pi.one_apply]
  refine Set.pi_congr rfl ?_
  intro i _
  by_cases hi : i = w₀
  · rw [hi, if_pos rfl]
    exact closure_Ioc zero_ne_one
  · rw [if_neg hi]
    exact closure_Ico zero_ne_one

theorem closure_box₂ :
    closure (box₂ K) = Set.univ.pi fun _ ↦ Set.Icc (-π) π := by
  rw [closure_pi_set]
  refine Set.pi_congr rfl ?_
  intro _ _
  refine closure_Ioc ?_
  rw [ne_eq, CharZero.neg_eq_self_iff]
  exact Real.pi_ne_zero

theorem interior_box₁ :
    interior (box₁ K) = Set.univ.pi fun _ ↦ Set.Ioo 0 1 := by
  rw [interior_pi_set Set.finite_univ]
  refine Set.pi_congr rfl ?_
  intro i _
  by_cases hi : i = w₀
  · rw [hi, if_pos rfl]
    exact interior_Ioc
  · rw [if_neg hi]
    exact interior_Ico

theorem interior_box₂ :
    interior (box₂ K) = Set.univ.pi fun _ ↦ Set.Ioo (-π) π := by
  rw [interior_pi_set Set.finite_univ]
  refine Set.pi_congr rfl ?_
  intro _ _
  exact interior_Ioc

theorem interior_subset_mapToUnitsPowComplex_source :
    interior (box K) ⊆ (mapToUnitsPowComplex K).source := by
  rw [interior_prod_eq, interior_box₁, interior_box₂, mapToUnitsPowComplex_source]
  exact Set.prod_mono (fun _ h ↦ (h w₀ (Set.mem_univ _)).1) subset_rfl

theorem isClosed_mapToUnitsPowComplex_closure_box :
    IsClosed (mapToUnitsPowComplex K '' (closure (box K))) := by
  classical
  refine (IsCompact.image_of_continuousOn ?_ ?_).isClosed
  · refine Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, Metric.isBounded_closure_iff.mpr ?_⟩
    exact (isBounded_box₁ K).prod (isBounded_box₂ K)
  · exact (continuous_mapToUnitsPowComplex K).continuousOn

theorem closure_subset_closure :
    closure (normLessThanOnePlus K) ⊆ mapToUnitsPowComplex K '' (closure (box K)) := by
  classical
  refine closure_minimal ?_ ?_
  · rw [normLessThanOnePlus_eq_image]
    refine Set.image_mono ?_
    exact subset_closure
  · exact isClosed_mapToUnitsPowComplex_closure_box K

theorem isOpen_mapToUnitsPowComplex_interior_box :
    IsOpen (mapToUnitsPowComplex K '' (interior (box K))) :=
  (mapToUnitsPowComplex K).isOpen_image_of_subset_source isOpen_interior
    (interior_subset_mapToUnitsPowComplex_source K)

theorem interior_subset_interior :
    mapToUnitsPowComplex K '' (interior (box K)) ⊆ interior (normLessThanOnePlus K) := by
  refine interior_maximal ?_ (isOpen_mapToUnitsPowComplex_interior_box K)
  rw [normLessThanOnePlus_eq_image]
  exact Set.image_mono interior_subset

open Classical in
theorem volume_interior_eq_volume_closure :
    volume (mapToUnitsPowComplex K '' (interior (box K))) =
      volume (mapToUnitsPowComplex K '' (closure (box K))) := by
  have hm₁ : MeasurableSet
      (mapToUnitsPowComplex K '' (Set.univ.pi fun x ↦ Set.Ioo 0 1) ×ˢ
        Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
    rw [← interior_box₁, ← interior_box₂, ← interior_prod_eq]
    exact (isOpen_mapToUnitsPowComplex_interior_box K).measurableSet
  have hm₂ : MeasurableSet
      (mapToUnitsPowComplex K '' Set.Icc 0 1 ×ˢ Set.univ.pi fun _ ↦ Set.Icc (-π) π) := by
    rw [← closure_box₁, ← closure_box₂, ← closure_prod_eq]
    exact (isClosed_mapToUnitsPowComplex_closure_box K).measurableSet
  have h₁ : Set.Icc 0 1 ⊆ {x : InfinitePlace K → ℝ | 0 ≤ x w₀} :=
    fun _ h ↦ (Set.mem_Icc.mp h).1 w₀
  have h₂ : Set.univ.pi (fun _ : InfinitePlace K ↦ Set.Ioo (0 : ℝ) 1) ⊆ {x | 0 ≤ x w₀} :=
    fun _ h ↦ (h w₀ (Set.mem_univ _)).1.le
  have h₃ : MeasurableSet (Set.univ.pi fun _ : InfinitePlace K ↦ Set.Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo
  rw [closure_prod_eq, interior_prod_eq, closure_box₁, closure_box₂, interior_box₁, interior_box₂,
    volume_mapToUnitsPowComplex_set_prod_set K h₃ h₂ (MeasurableSet.univ_pi fun _ ↦
    measurableSet_Ioo) (Set.pi_mono fun _ _ ↦ Set.Ioo_subset_Icc_self) hm₁,
    volume_mapToUnitsPowComplex_set_prod_set K measurableSet_Icc h₁ (MeasurableSet.univ_pi fun _ ↦
    measurableSet_Icc) le_rfl hm₂]
  simp_rw [setLIntegral_mapToUnitsPow K h₃ h₂, setLIntegral_mapToUnitsPow K measurableSet_Icc h₁,
    mul_assoc, ← Set.pi_inter_distrib, Set.inter_self, Set.inter_eq_left.mpr
      Set.Ioo_subset_Icc_self]
  congr 5
  refine Measure.restrict_congr_set ?_
  rw [show (Set.univ.pi fun _ ↦ Set.Ioo (0 : ℝ) 1) = interior (Set.Icc 0 1) by
        simp_rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ, Pi.zero_apply, Pi.one_apply,
        interior_Icc]]
  exact interior_ae_eq_of_null_frontier ((convex_Icc 0 1).addHaar_frontier volume)

theorem volume_normLessThanOnePlus_aux (n : ℕ) :
    ∫⁻ x in box₁ K, ENNReal.ofReal |x w₀| ^ n = (n + 1 : ENNReal)⁻¹ := by
  classical
  rw [volume_pi, box₁, measure_restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ ?_ (Finset.mem_univ w₀)]
  simp_rw [if_true, Function.update_same]
  have : ∫⁻ (xᵢ : ℝ) in Set.Ioc 0 1, ENNReal.ofReal |xᵢ| ^ n = (n + 1 : ENNReal)⁻¹ := by
    convert congr_arg ENNReal.ofReal (integral_pow (a := 0) (b := 1) n)
    · rw [intervalIntegral.integral_of_le zero_le_one]
      rw [ofReal_integral_eq_lintegral_ofReal]
      · refine setLIntegral_congr_fun measurableSet_Ioc ?_
        filter_upwards with _ h using by rw [abs_of_pos h.1, ENNReal.ofReal_pow h.1.le]
      · refine IntegrableOn.integrable ?_
        rw [← Set.uIoc_of_le zero_le_one, ← intervalIntegrable_iff]
        exact intervalIntegral.intervalIntegrable_pow n
      · exact ae_restrict_of_forall_mem measurableSet_Ioc fun _ h ↦ pow_nonneg h.1.le _
    · rw [one_pow, zero_pow (by linarith), sub_zero, ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one, ENNReal.ofReal_natCast,
        one_div]
  rw [this]
  rw [lmarginal]
  rw [lintegral_const]
  rw [pi_univ]
  rw [Finset.prod_congr rfl (g := fun _ ↦ 1) (fun x _ ↦ by rw [if_neg (by aesop), restrict_apply
    MeasurableSet.univ, Set.univ_inter, Real.volume_Ico, sub_zero, ENNReal.ofReal_one])]
  rw [prod_const_one, mul_one]
  fun_prop

open Classical in
theorem volume_normLessThanOnePlus : volume (normLessThanOnePlus K) =
    NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := by
  rw [normLessThanOnePlus_eq_image, volume_mapToUnitsPowComplex_set_prod_set K
    (measurableSet_box₁ K) (fun _ h ↦ le_of_lt (pos_of_mem_box₁ K h)) (measurableSet_box₂ K)
    (Set.pi_mono fun _ _ ↦ Set.Ioc_subset_Icc_self)
    (by rw [← normLessThanOnePlus_eq_image]; exact normLessThanOnePlus_measurableSet K),
    setLIntegral_mapToUnitsPow K (measurableSet_box₁ K) (fun _ h ↦ ((if_pos rfl) ▸
      Set.mem_univ_pi.mp h w₀).1.le), Set.inter_eq_left.mpr (Set.pi_mono fun _ _ ↦
    Set.Ioo_subset_Ioc_self), volume_pi_pi]
  simp_rw [Real.volume_Ioo, sub_neg_eq_add, ← two_mul, prod_const, ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_ofNat, mul_pow]
  have h₁ : ∀ x : InfinitePlace K → ℝ,
      0 < ∏ i : {w // IsComplex w}, (mapToUnitsPow₀ K) (fun w ↦ x w) i.val :=
    fun _ ↦ Finset.prod_pos fun _ _ ↦ mapToUnitsPow₀_pos K _ _
  have h₂ : rank K + NrComplexPlaces K + 1 = finrank ℚ K := by
    rw [rank, add_comm _ 1, ← add_assoc, add_tsub_cancel_of_le NeZero.one_le,
      card_eq_nrRealPlaces_add_nrComplexPlaces,  ← card_add_two_mul_card_eq_rank]
    ring
  calc
    _ = (NNReal.pi : ENNReal) ^ NrComplexPlaces K * (regulator K).toNNReal * (finrank ℚ K) *
          ∫⁻ x in box₁ K, ENNReal.ofReal |x w₀| ^ (rank K + NrComplexPlaces K) := by
      simp_rw [← mul_assoc]
      congr
      · rw [mul_comm, ← mul_assoc, NrComplexPlaces, card_univ, ← mul_pow, ENNReal.inv_mul_cancel
          two_ne_zero ENNReal.two_ne_top, one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal,
          NNReal.coe_real_pi]
      · ext x
        simp_rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul, Real.toNNReal_mul (abs_nonneg _),
          ENNReal.coe_mul, ENNReal.coe_RealtoNNReal]
        rw [Finset.prod_mul_distrib, Finset.prod_const, mul_mul_mul_comm,
          ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (mapToUnitsPow₀_pos K _ _).le),
          ENNReal.ofReal_inv_of_pos (h₁ x), ENNReal.inv_mul_cancel
          (ENNReal.ofReal_ne_zero_iff.mpr (h₁ x)) ENNReal.ofReal_ne_top, mul_one, pow_add,
          NrComplexPlaces, card_univ]
    _ = NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := by
      rw [volume_normLessThanOnePlus_aux, ← Nat.cast_add_one, h₂, mul_assoc, ENNReal.mul_inv_cancel,
        mul_one]
      · rw [Nat.cast_ne_zero]
        refine ne_of_gt ?_
        exact finrank_pos
      · exact ENNReal.natCast_ne_top _

open Classical in
theorem volume_frontier_normLessThanOnePlus :
    volume (frontier (normLessThanOnePlus K)) = 0 := by
  rw [frontier, measure_diff]
  have : volume (closure (normLessThanOnePlus K)) = volume (interior (normLessThanOnePlus K)) := by
    refine le_antisymm ?_ (measure_mono interior_subset_closure)
    refine le_trans ?_ (measure_mono (interior_subset_interior K))
    rw [volume_interior_eq_volume_closure]
    exact measure_mono (closure_subset_closure K)
  refine tsub_eq_zero_iff_le.mpr (le_of_eq this)
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
  · rw [← lt_top_iff_ne_top]
    refine lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLessThanOnePlus]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

theorem negAt_normLessThanOne (s : Finset {w // IsReal w}) :
    (negAt s) '' normLessThanOne K ⊆ normLessThanOne K := by
  rintro _ ⟨x, hx, rfl⟩
  exact mem_normLessThanOne_of_normAtPlace_eq hx fun w ↦ normAtPlace_negAt_eq _ _ _

open Classical in
theorem volume_normLessThanOne :
    volume (normLessThanOne K) =
      2 ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := by
  rw [main]
  rw [volume_normLessThanOnePlus, mul_assoc]
  · exact measurableSet_normLessThanOne K
  · exact fun s ↦ negAt_normLessThanOne K s

theorem part₀_normLessThanOne :
    part₀ (normLessThanOne K) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro x ⟨hx₁, hx₂⟩
  rw [Set.mem_iUnion] at hx₂
  obtain ⟨w, hw⟩ := hx₂
  have := normAtPlace_pos_of_mem hx₁.1 w
  rw [normAtPlace_apply_isReal w.prop, hw, norm_zero] at this
  exact (lt_irrefl _) this

open Classical in
theorem volume_frontier_normLessThanOne :
    volume (frontier (normLessThanOne K)) = 0 := by
  rw [res21 (normLessThanOne K) (fun s ↦ negAt_normLessThanOne K s)]
  rw [part₀_normLessThanOne, Set.union_empty]
  refine measure_mono_null (frontier_iUnion _) (measure_iUnion_null_iff.mpr fun s ↦ ?_)
  rw [negAtPlus_eq_preimage]
  rw [← ContinuousLinearEquiv.coe_toHomeomorph, ← Homeomorph.preimage_frontier,
    ContinuousLinearEquiv.coe_toHomeomorph, (volume_preserving_negAt s).measure_preimage
    measurableSet_frontier.nullMeasurableSet]
  exact volume_frontier_normLessThanOnePlus K

end fundamentalCone

end NumberField.mixedEmbedding

namespace NumberField.mixedEmbedding.euclideanSpace

open NumberField NumberField.InfinitePlace MeasureTheory BigOperators Submodule

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

/-- Docs. -/
local instance : Ring (EuclideanSpace ℝ { w : InfinitePlace K // IsReal w }) := Pi.ring

/-- Docs. -/
local instance : Ring (EuclideanSpace ℂ { w : InfinitePlace K // IsComplex w }) := Pi.ring

instance : Ring (E₂ K) := Prod.instRing

instance : MeasurableSpace (E₂ K) := borel _

instance : BorelSpace (E₂ K)  :=  ⟨rfl⟩

open Classical in
instance : T2Space (E₂ K) := Prod.t2Space

open Classical in
protected theorem norm_apply (x : E₂ K) :
    ‖x‖ = Real.sqrt (∑ w, ‖x.1 w‖ ^ 2 + ∑ w, ‖x.2 w‖ ^ 2) := by
  rw [WithLp.prod_norm_eq_add (by exact Nat.ofNat_pos), EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq, ENNReal.toReal_ofNat, Real.rpow_two, Real.sq_sqrt (by positivity),
    Real.rpow_two, Real.sq_sqrt (by positivity), Real.sqrt_eq_rpow]

-- protected theorem inner_apply (x y : E₂ K) :
--     ⟪x, y⟫_ℝ = ∑ w, (x.1 w) * (y.1 w) +
--       ∑ w, ((x.2 w).re * (y.2 w).re + (x.2 w).im * (y.2 w).im) := by
--   simp_rw [WithLp.prod_inner_apply, EuclideanSpace.inner_eq_star_dotProduct, real_inner_eq_re_inner,
--     EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct, Pi.star_apply, star_trivial,
--     RCLike.star_def, map_sum, RCLike.mul_re, RCLike.conj_re, RCLike.re_to_complex,
--     RCLike.conj_im, WithLp.equiv_pi_apply, neg_mul, sub_neg_eq_add, RCLike.im_to_complex]

/-- Docs. -/
protected def linearEquiv : (E₂ K) ≃ₗ[ℝ] (E K) := WithLp.linearEquiv _ _ _

open Classical in
/-- Docs. -/
def CLE : (E₂ K) ≃L[ℝ] (E K) :=
  (euclideanSpace.linearEquiv K).toContinuousLinearEquiv

/-- Docs. -/
protected def homeomorph : (E₂ K) ≃ₜ (E K) :=
  (euclideanSpace.CLE K).toHomeomorph

/-- Docs. -/
-- protected def addEquiv : (E₂ K) ≃+ (E K) := (euclideanSpace.linearEquiv K).toAddEquiv

protected theorem coe_homeomorph :
   ⇑(CLE K) = ⇑(euclideanSpace.homeomorph K) := rfl

protected theorem coe_linearEquiv :
    ⇑(CLE K) = ⇑(euclideanSpace.linearEquiv K) := rfl

@[simp]
theorem CLE_apply_ofIsReal (x : E₂ K) {w : InfinitePlace K} (hw : IsReal w) :
    (CLE K x).1 ⟨w, hw⟩ = x.1 ⟨w, hw⟩ := rfl

@[simp]
theorem linearEquiv_apply_ofIsComplex (x : E₂ K) {w : InfinitePlace K} (hw : IsComplex w) :
    (CLE K x).2 ⟨w, hw⟩ = x.2 ⟨w, hw⟩ := rfl

instance : Nontrivial (E₂ K) := (CLE K).toEquiv.nontrivial

protected theorem finrank :
    FiniteDimensional.finrank ℝ (E₂ K) = FiniteDimensional.finrank ℚ K := by
  rw [← mixedEmbedding.finrank]
  refine  LinearEquiv.finrank_eq ?_
  exact euclideanSpace.linearEquiv K

open Classical in
/-- Docs. -/
protected def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (E₂ K) :=
  OrthonormalBasis.prod (EuclideanSpace.basisFun _ ℝ)
    ((Pi.orthonormalBasis fun _ ↦ Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

open Classical in
theorem stdOrthonormalBasis_map_equiv :
    (euclideanSpace.stdOrthonormalBasis K).toBasis.map (CLE K) =
      mixedEmbedding.stdBasis K := by ext _ _ <;> rfl

open Classical in
@[simp]
theorem stdOrthonormalBasis_repr_apply (x : E₂ K) (i : index K) :
    (euclideanSpace.stdOrthonormalBasis K).repr x i =
      (stdBasis K).repr (CLE K x) i := rfl

open Classical in
theorem volumePreserving_CLE :
    MeasurePreserving (CLE K) := by
  let e := (euclideanSpace.homeomorph K).toMeasurableEquiv
  convert e.measurable.measurePreserving volume
  erw [← (OrthonormalBasis.addHaar_eq_volume (euclideanSpace.stdOrthonormalBasis K)),
    Homeomorph.toMeasurableEquiv_coe, Basis.map_addHaar _ (CLE K),
    stdOrthonormalBasis_map_equiv, eq_comm, Basis.addHaar_eq_iff, Basis.coe_parallelepiped,
    ← measure_congr (Zspan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume),
    volume_fundamentalDomain_stdBasis K]

end NumberField.mixedEmbedding.euclideanSpace

open Filter NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Topology MeasureTheory
  NumberField.Units NumberField.mixedEmbedding.fundamentalCone Submodule Bornology
  NumberField.mixedEmbedding.euclideanSpace FiniteDimensional NumberField.Units.dirichletUnitTheorem

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- Docs. -/
abbrev Λ : AddSubgroup (E₂ K) :=
    (span ℤ (Set.range ((latticeBasis K).map (CLE K).symm))).toAddSubgroup

open Classical in
instance : DiscreteTopology (Λ K) := Zspan.instDiscreteTopology _

open Classical in
instance : IsZlattice ℝ (Λ K) where
  span_top := by
    simp_rw [Λ, coe_toAddSubgroup, ← Zspan.map, map_coe, LinearEquiv.restrictScalars_apply,
      ← Submodule.map_span, Zspan.span_top, Submodule.map_top, LinearEquivClass.range]

/-- Docs. -/
abbrev X : Set (E₂ K) := (CLE K)⁻¹' (fundamentalCone K)

/-- Docs. -/
abbrev X₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (CLE K x) ≤ 1}

theorem aux₁ :
    {x ∈ X K | mixedEmbedding.norm (CLE K x) ≤ 1} = (CLE K)⁻¹' (normLessThanOne K) := by
  simp only [Set.mem_preimage, normLessThanOne, Set.preimage_setOf_eq]

theorem aux₂ :
    (Λ K : Set (E₂ K)) ∩ (X K) = (CLE K)⁻¹' (integralPoint K) := by
  classical
  rw [integralPoint, Set.inter_comm _ (X K), Set.preimage_inter]
  congr
  ext x
  rw [Λ]
  rw [coe_toAddSubgroup, SetLike.mem_coe]
  rw [Set.mem_preimage, ← Set.range_comp, ← RingHom.coe_comp, ← RingHom.coe_range]
  rw [SetLike.mem_coe]
  rw [← mem_span_latticeBasis]
  rfl

open Classical in
theorem volume_X₁ :
    (volume (X₁ K)).toReal = 2 ^ NrRealPlaces K * π^ NrComplexPlaces K *
      (regulator K) := by
  rw [X₁, aux₁, (volumePreserving_CLE K).measure_preimage
    (measurableSet_normLessThanOne K).nullMeasurableSet, volume_normLessThanOne, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.coe_toReal, Real.coe_toNNReal _
    (regulator_pos K).le]

open Classical in
theorem covolume_Λ :
    Zlattice.covolume (Λ K) = (2 : ℝ)⁻¹ ^ NrComplexPlaces K * Real.sqrt |discr K| := by
  have : IsAddFundamentalDomain (Λ K) ((CLE K) ⁻¹' Zspan.fundamentalDomain (latticeBasis K)) := by
    rw [euclideanSpace.coe_linearEquiv, ← LinearEquiv.image_symm_eq_preimage,
      Zspan.map_fundamentalDomain]
    have : Λ K =
        (span ℤ (Set.range ((latticeBasis K).map
          (euclideanSpace.linearEquiv K).symm))).toAddSubgroup := by
      rfl
    rw [this]
    exact Zspan.isAddFundamentalDomain _ volume
  rw [Zlattice.covolume_eq_measure_fundamentalDomain (Λ K) volume this,
    (volumePreserving_CLE K).measure_preimage
    (Zspan.fundamentalDomain_measurableSet (latticeBasis K)).nullMeasurableSet,
    volume_fundamentalDomain_latticeBasis,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]

open Submodule Ideal nonZeroDivisors

open Classical in
theorem final₁ :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ n} * torsionOrder K : ℝ) / n) atTop
          (𝓝 ((volume (X₁ K)).toReal / Zlattice.covolume (Λ K))) := by
  refine Tendsto.congr' ?_
    (Tendsto.comp (Zlattice.covolume.tendsto_card_le_div' (Λ K) ?_ ?_ ?_ ?_ ?_)
      tendsto_natCast_atTop_atTop)
  · filter_upwards with n
    have := card_isPrincipal_norm_le K n
    simp_rw [Function.comp_apply, ← Nat.cast_mul]
    rw [this]
    simp_rw [Set.setOf_inter_eq_sep, ← and_assoc, ← Set.mem_inter_iff]
    congr 2
    refine Nat.card_congr ?_
    rw [@Set.coe_setOf, Set.coe_setOf]
    simp_rw [intNorm_le_iff]
    refine Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeInter
      (· ∈ integralPoint K) (fun a ↦ mixedEmbedding.norm a ≤ n)).symm
    refine Equiv.subtypeEquiv (CLE K).toEquiv ?_
    intro x
    rw [aux₂]
    simp
  · intro x r hx hr
    rwa [Set.mem_preimage, _root_.map_smul, (smul_mem_iff_mem (ne_of_lt hr).symm)]
  · intro x r hr
    rw [_root_.map_smul, mixedEmbedding.norm_smul, euclideanSpace.finrank, abs_of_pos hr]
  · exact isBounded_normLessThanOne K
  · exact (CLE K).continuous.measurable (measurableSet_normLessThanOne K)
  · rw [aux₁, euclideanSpace.coe_homeomorph, ← Homeomorph.preimage_frontier,
      ←  euclideanSpace.coe_homeomorph, (volumePreserving_CLE K).measure_preimage]
    exact volume_frontier_normLessThanOne K
    refine  measurableSet_frontier.nullMeasurableSet

open Classical in
theorem final₂ :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) / n) atTop
          (𝓝 ((2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  convert (final₁ K).mul (tendsto_const_nhds (x := (torsionOrder K : ℝ)⁻¹)) using 2
  · rw [mul_comm_div, mul_assoc, ← mul_div_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
      (torsionOrder K).ne_zero), mul_one_div]
  · rw [volume_X₁, covolume_Λ]
    ring_nf

end

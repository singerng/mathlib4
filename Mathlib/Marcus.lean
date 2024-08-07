import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Finset
  NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional MeasureTheory.Measure

open scoped Real ENNReal ComplexOrder

namespace NumberField.mixedEmbedding.fundamentalCone

noncomputable section

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

variable {K}

def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def realToMixed : (InfinitePlace K → ℝ) →L[ℝ] (E K) := ContinuousLinearMap.prod
  (ContinuousLinearMap.pi fun w ↦ ContinuousLinearMap.proj w.val)
  (ContinuousLinearMap.pi fun w ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj w.val))

@[simp]
theorem normAtPlace_realToMixed (w : InfinitePlace K) (x : InfinitePlace K → ℝ) :
    normAtPlace w (realToMixed x) = |x w| := by
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtPlace_apply_isReal hw, realToMixed]
  · simp [normAtPlace_apply_isComplex hw, realToMixed]

@[simp]
theorem norm_realToMixed (x : InfinitePlace K → ℝ) :
    mixedEmbedding.norm (realToMixed x) = ∏ w, |x w| ^ w.mult :=
  Finset.prod_congr rfl fun w _ ↦ by simp

theorem pos_norm_realToMixed {x : InfinitePlace K → ℝ} (hx : ∀ w, 0 < x w) :
    0 < mixedEmbedding.norm (realToMixed x) := by
  rw [norm_realToMixed]
  exact Finset.prod_pos fun w _ ↦ pow_pos (abs_pos_of_pos (hx w)) _

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
    rw [Set.mem_setOf_eq, ← Finset.univ.sum_erase_add _ (Finset.mem_univ w₀), dif_pos rfl]
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
  rw [← Real.log_rpow (hx _), Real.exp_log (Real.rpow_pos_of_pos (hx _) _), abs_of_pos (hx _),
    Real.rpow_natCast]

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

open Classical in
theorem mapToUnitsPow₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ (c i) := by
  ext w
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply,
    LinearEquiv.coe_toEquiv, mapToUnitsPow₀_aux, Function.comp_apply, Basis.equivFun_symm_apply,
    Basis.coe_reindex, Function.comp_apply, Basis.ofZlatticeBasis_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, neg_mul, ← logEmbedding_fundSystem, Finset.mul_sum]
  by_cases hw : w = w₀
  · rw [dif_pos hw, Finset.sum_comm, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp_rw [← Finset.mul_sum, sum_logEmbedding_component, ← mul_assoc, mul_comm _ (c _),
      mul_assoc (c _), hw, mul_neg, neg_mul, mul_neg, neg_neg, inv_mul_cancel mult_coe_ne_zero,
      one_mul]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← Real.log_rpow (pos_iff.mpr (by simp)),
      Real.exp_log (by exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]
  · rw [dif_neg hw, Real.exp_sum]
    congr with x
    rw [logEmbedding_component, ← mul_assoc, ← mul_assoc, mul_comm _ (c _), mul_assoc (c _),
      inv_mul_cancel mult_coe_ne_zero, mul_one, ← Real.log_rpow (pos_iff.mpr (by simp)),
      Real.exp_log (Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _)]

theorem mapToUnitsPow₀_ne_zero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact Function.ne_iff.mpr ⟨w, ne_of_gt (mapToUnitsPow₀_pos K c w)⟩

-- theorem mapToUnitsPow₀_symm_apply {x : InfinitePlace K → ℝ}
--     (hx : mixedEmbedding.norm (realToMixed x) = 1) :
--     (mapToUnitsPow₀_aux K).symm x = logMap (realToMixed x) := by
--   ext w
--   rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
--     normAtPlace_realToMixed, Real.log_abs]

open Classical in
theorem mapToUnitsPow₀_symm_apply {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    (mapToUnitsPow₀ K).symm x = (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex
      equivFinRank).equivFun (logMap (realToMixed x)) := by
  rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, EquivLike.coe_coe, Function.comp_apply]
  congr with x
  rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
    normAtPlace_realToMixed, Real.log_abs]

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
          ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), mul_inv_cancel
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
abbrev mapToUnitsPow_single (c : (InfinitePlace K → ℝ)) : InfinitePlace K → (InfinitePlace K → ℝ) :=
  fun i ↦ if hi : i = w₀ then fun _ ↦ |c w₀| else
    fun w ↦ (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ (c i)

open Classical in
theorem mapToUnitsPow₀_eq_prod_single (c : (InfinitePlace K → ℝ)) (w : InfinitePlace K) :
    mapToUnitsPow₀ K (fun w ↦ c w.val) w =
      ∏ i ∈ univ.erase w₀, mapToUnitsPow_single K c i w := by
  rw [mapToUnitsPow₀_apply, Finset.prod_subtype (Finset.univ.erase w₀)
    (fun w ↦ (by aesop : w ∈ univ.erase w₀ ↔ w ≠ w₀))]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [mapToUnitsPow_single, dif_neg w.prop]

theorem mapToUnitsPow_eq_prod_single (c : (InfinitePlace K → ℝ)) (w : InfinitePlace K) :
    mapToUnitsPow K c w = ∏ i, mapToUnitsPow_single K c i w := by
  classical
  rw [← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀), mapToUnitsPow_apply, Pi.smul_apply,
    mapToUnitsPow₀_eq_prod_single, smul_eq_mul, mapToUnitsPow_single, dif_pos rfl]

theorem mapToUnitsPow_nonneg (c : (InfinitePlace K → ℝ)) (w : InfinitePlace K) :
    0 ≤ mapToUnitsPow K c w :=
  mul_nonneg (abs_nonneg _) (mapToUnitsPow₀_pos K _ _).le

theorem mapToUnitsPow_zero_iff (c : (InfinitePlace K → ℝ)) (w : InfinitePlace K) :
    mapToUnitsPow K c w = 0 ↔ c w₀ = 0 := by
  rw [mapToUnitsPow_apply, Pi.smul_apply, smul_eq_mul, mul_eq_zero, abs_eq_zero,
    or_iff_left (ne_of_gt (mapToUnitsPow₀_pos K _ _))]

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
  · rw [abs_of_pos (mapToUnitsPow₀_pos K c _), mult, if_pos w.prop, pow_one]
  · rw [abs_of_pos (mapToUnitsPow₀_pos K c _), mult, if_neg w.prop]

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
    · rw [inv_mul_cancel mult_coe_ne_zero]
    · rw [← mul_assoc, mul_comm _ (c w₀), mul_assoc, inv_mul_cancel_left₀ mult_coe_ne_zero,
        abs_eq_self.mpr hc]

open ENNReal Classical in
theorem setLIntegral_mapToUnitsPow {s : Set (InfinitePlace K → ℝ)} (hs₀ : MeasurableSet s)
    (hs₁ : s ⊆ {x | 0 < x w₀}) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (mapToUnitsPow K) '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * ENNReal.ofReal (regulator K) * (finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
        (mapToUnitsPow₀ K (fun w ↦ x w) i))⁻¹ *
        ENNReal.ofReal |x w₀| ^ rank K * f (mapToUnitsPow K x) := by
  have hs₂ : s ⊆ {x | 0 ≤ x w₀} := subset_trans hs₁ fun _ h ↦ Set.mem_setOf.mpr (le_of_lt h)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs₀
    (fun c hc ↦ HasFDerivWithinAt.mono (hasFDeriv_mapToUnitsPow K c (hs₂ hc)) hs₂)
    ((mapToUnitsPow K).injOn.mono hs₁)]
  rw [setLIntegral_congr_fun hs₀ (ae_of_all volume fun c hc ↦ by rw [jacobian_det K (hs₂ hc)])]
  rw [← lintegral_const_mul']
  congr with x
  have : 0 ≤ (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K (fun w ↦ x w) w)⁻¹ :=
    inv_nonneg.mpr <| Finset.prod_nonneg fun w _ ↦ (mapToUnitsPow₀_pos K _ w).le
  rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
    ofReal_mul (by positivity), ofReal_natCast, ofReal_pow (by positivity), ofReal_pow
    (by positivity), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat]
  · ring_nf
  · exact mul_ne_top (mul_ne_top (pow_ne_top (inv_ne_top.mpr two_ne_zero)) ofReal_ne_top)
      (natCast_ne_top _)

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

-- marcus₃ -- WRONG NAME
def polarCoordToMixedSpace : PartialHomeomorph
    ((InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) (E K) :=
  (realProdComplexProdEquiv K).symm.transPartialHomeomorph <|
    (PartialHomeomorph.refl _).prod <| PartialHomeomorph.pi fun _ ↦ Complex.polarCoord.symm

def polarCoordToMixedSpace₀ : PartialHomeomorph
    (E K) ((InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  ((PartialHomeomorph.refl _).prod
    (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)).transHomeomorph (realProdComplexProdEquiv K)

theorem polarCoordToMixedSpace_apply (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    polarCoordToMixedSpace K x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := rfl

theorem polarCoordToMixedSpace₀_symm_apply (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    (polarCoordToMixedSpace₀ K).symm x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := rfl

theorem polarCoordToMixedSpace_symm_apply (x : E K) :
    (polarCoordToMixedSpace K).symm x =
      (realProdComplexProdEquiv K) (x.1, fun w ↦ Complex.polarCoord (x.2 w)) := by
  rw [polarCoordToMixedSpace]
  rw [Homeomorph.transPartialHomeomorph_symm_apply, Homeomorph.symm_symm,
    PartialHomeomorph.prod_symm, PartialHomeomorph.prod_apply, Function.comp_apply,
    PartialHomeomorph.refl_symm, PartialHomeomorph.refl_apply, id_eq]
  rfl

theorem polarCoordToMixedSpace₀_apply (x : E K) :
    polarCoordToMixedSpace₀ K x =
      (realProdComplexProdEquiv K) (x.1, fun w ↦ Complex.polarCoord (x.2 w)) := by
  rw [polarCoordToMixedSpace₀]
  simp_rw [PartialHomeomorph.transHomeomorph_apply, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Function.comp_apply]
  rfl

theorem measurable_polarCoordToMixedSpace :
    Measurable (polarCoordToMixedSpace K) := by
  change Measurable (fun x ↦ polarCoordToMixedSpace K x)
  simp_rw [polarCoordToMixedSpace_apply]
  refine Measurable.prod ?_ ?_
  · dsimp only
    exact measurable_pi_lambda _ fun x ↦ (measurable_pi_apply _).comp' measurable_fst
  · dsimp only
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop

theorem  measurable_polarCoordToMixedSpace₀_symm :
    Measurable (polarCoordToMixedSpace₀ K).symm := by
  change Measurable (fun x ↦ (polarCoordToMixedSpace₀ K).symm x)
  simp_rw [polarCoordToMixedSpace₀_symm_apply]
  refine Measurable.prod ?_ ?_
  · dsimp only
    exact measurable_pi_lambda _ fun x ↦ (measurable_pi_apply _).comp' measurable_fst
  · dsimp only
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop

open Classical in
theorem polarCoordToMixedSpace_source : (polarCoordToMixedSpace K).source =
  (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [polarCoordToMixedSpace, Homeomorph.transPartialHomeomorph_source]
  ext
  simp_rw [Set.mem_preimage, realProdComplexProdEquiv_symm_apply, PartialHomeomorph.prod_source,
    Set.mem_prod, PartialHomeomorph.refl_source, PartialHomeomorph.pi_source,
    PartialHomeomorph.symm_source, Complex.polarCoord_target]
  aesop

theorem polarCoordToMixedSpace₀_source :
    (polarCoordToMixedSpace₀ K).source = Set.univ ×ˢ Set.univ.pi fun _ ↦ Complex.slitPlane := by
  simp [polarCoordToMixedSpace₀, Complex.polarCoord_source]

open Classical in
theorem polarCoordToMixedSpace₀_target : (polarCoordToMixedSpace₀ K).target =
  (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [polarCoordToMixedSpace₀, PartialHomeomorph.transHomeomorph_target]
  ext
  simp_rw [Set.mem_preimage, realProdComplexProdEquiv_symm_apply, PartialHomeomorph.prod_target,
    Set.mem_prod, PartialHomeomorph.refl_target, PartialHomeomorph.pi_target,
    Complex.polarCoord_target]
  aesop

theorem polarCoordToMixedSpace_target :
    (polarCoordToMixedSpace K).target = Set.univ ×ˢ Set.univ.pi fun _ ↦ Complex.slitPlane := by
  simp [polarCoordToMixedSpace, Complex.polarCoord_source]

theorem measurableSet_polarCoordToMixedSpace₀_target :
    MeasurableSet (polarCoordToMixedSpace₀ K).target := by
  rw [polarCoordToMixedSpace₀_target]
  refine MeasurableSet.prod ?_ ?_
  · refine MeasurableSet.univ_pi ?_
    intro w
    refine MeasurableSet.ite' ?_ ?_
    · intro _
      exact MeasurableSet.univ
    · intro _
      exact measurableSet_Ioi
  · refine MeasurableSet.univ_pi ?_
    intro _
    exact measurableSet_Ioo

theorem measurableSet_polarCoordToMixedSpace_source :
    MeasurableSet (polarCoordToMixedSpace K).source := by
  rw [polarCoordToMixedSpace_source]
  refine MeasurableSet.prod ?_ ?_
  · refine MeasurableSet.univ_pi ?_
    intro w
    refine MeasurableSet.ite' ?_ ?_
    · intro _
      exact MeasurableSet.univ
    · intro _
      exact measurableSet_Ioi
  · refine MeasurableSet.univ_pi ?_
    intro _
    exact measurableSet_Ioo

theorem realProdComplexProdEquiv_preimage_polarCoordToMixedSpace₀_target :
  (realProdComplexProdEquiv K) ⁻¹' (polarCoordToMixedSpace₀ K).target =
    Set.univ ×ˢ Set.univ.pi fun _ ↦ polarCoord.target := by
  ext
  simp_rw [polarCoordToMixedSpace₀_target, Set.mem_preimage, realProdComplexProdEquiv_apply,
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

theorem realProdComplexProdEquiv_preimage_polarCoordToMixedSpace_source :
  (realProdComplexProdEquiv K) ⁻¹' (polarCoordToMixedSpace K).source =
    Set.univ ×ˢ Set.univ.pi fun _ ↦ polarCoord.target := by
  ext
  simp_rw [polarCoordToMixedSpace_source, Set.mem_preimage, realProdComplexProdEquiv_apply,
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
      ∫⁻ x in (polarCoordToMixedSpace₀ K).target,
        (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal) *
          f ((polarCoordToMixedSpace₀ K).symm x) := by
  have h : Measurable fun x ↦ (∏ w : { w // IsComplex w}, (x.1 w.val).toNNReal) *
      f ((polarCoordToMixedSpace₀ K).symm x) := by
    refine Measurable.mul ?_ ?_
    · exact measurable_coe_nnreal_ennreal_iff.mpr <| Finset.measurable_prod _ fun _ _ ↦ by fun_prop
    · exact hf.comp' (measurable_polarCoordToMixedSpace K)
  rw [← (volume_preserving_realProdComplexProdEquiv K).setLIntegral_comp_preimage
    (measurableSet_polarCoordToMixedSpace₀_target K) h, volume_eq_prod, volume_eq_prod,
    lintegral_prod _ hf.aemeasurable]
  simp_rw [Complex.lintegral_pi_comp_polarCoord_symm _ (hf.comp' measurable_prod_mk_left)]
  rw [realProdComplexProdEquiv_preimage_polarCoordToMixedSpace₀_target,
    ← Measure.restrict_prod_eq_univ_prod, lintegral_prod _
    (h.comp' (realProdComplexProdEquiv K).measurable).aemeasurable]
  simp_rw [realProdComplexProdEquiv_apply, polarCoordToMixedSpace₀_symm_apply,
    dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]

def mapToUnitsPowComplex : PartialHomeomorph
    ((InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) (E K) :=
  PartialHomeomorph.trans
    (PartialHomeomorph.prod (mapToUnitsPow K) (PartialHomeomorph.refl _))
    (polarCoordToMixedSpace₀ K).symm

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
    polarCoordToMixedSpace_source, Set.mem_prod, mapToUnitsPow_source]
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
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.trans_target, polarCoordToMixedSpace_target,
    PartialHomeomorph.prod_target, PartialHomeomorph.refl_target, Set.mem_inter_iff,
    Set.mem_preimage, mapToUnitsPow_target, Set.mem_prod, Set.mem_univ, true_and, and_true,
    and_comm]
  rw [and_congr_right]
  intro h
  simp_rw [polarCoordToMixedSpace_symm_apply, realProdComplexProdEquiv_apply, Set.mem_pi,
    Set.mem_univ, true_implies]
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

theorem mapToUnitsPowComplex_image_prod (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    mapToUnitsPowComplex K '' (s ×ˢ t) =
      polarCoordToMixedSpace K '' (mapToUnitsPow K '' s) ×ˢ t := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.coe_trans, Function.comp_apply,
    PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq,
    polarCoordToMixedSpace_apply, Set.mem_image, Set.mem_prod, Prod.exists]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨mapToUnitsPow K x, y, ⟨Set.mem_image_of_mem _ hx, hy⟩, rfl⟩
  · rintro ⟨_, y, ⟨⟨⟨x, hx, rfl⟩, hy⟩, rfl⟩⟩
    exact ⟨x, y, ⟨hx, hy⟩, rfl⟩

open Classical in
theorem toto {s : Set (InfinitePlace K → ℝ)} {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)}
    (hs : s ⊆ {x | ∀ w, 0 ≤ x w}) (ht : t ⊆ Set.univ.pi fun _ ↦ Set.Icc (-π) π) :
    (fun x ↦ (mapToUnitsPowComplex K '' s ×ˢ t).indicator (fun x ↦ (1 : ENNReal))
      (polarCoordToMixedSpace K x)) =ᵐ[volume]
        fun x ↦ (mapToUnitsPow K '' s).indicator 1 x.1 * t.indicator 1 x.2 := by


theorem normVector_mapToUnitsPowComplex (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    (fun w ↦ normAtPlace w (mapToUnitsPowComplex K x)) = mapToUnitsPow K x.1 := by
  rw [mapToUnitsPowComplex_apply]
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_isReal hw, Real.norm_eq_abs, abs_eq_self.mpr (mapToUnitsPow_nonneg K _ _)]
  · rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.polarCoord_symm_abs,
      abs_eq_self.mpr (mapToUnitsPow_nonneg K _ _)]

open Classical in
theorem volume_mapToUnitsPowComplex_set_prod_set {s : Set (InfinitePlace K → ℝ)}
    {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)} (hs : s ⊆ {x | ∀ w, 0 ≤ x w})
    (ht : t ⊆ Set.univ.pi fun _ ↦ Set.Icc (-π) π) :
    volume (mapToUnitsPowComplex K '' (s ×ˢ t)) =
      volume t * ∫⁻ x in mapToUnitsPow K '' s,
        ∏ w : { w : InfinitePlace K // w.IsComplex }, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator, lintegral_mixedSpace_eq]
  simp only [ENNReal.coe_finset_prod]
  have := toto K hs ht
  have := Filter.EventuallyEq.mul
    (Filter.EventuallyEq.refl _ (fun x ↦ (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal))) this
  rw [setLIntegral_congr_fun sorry ((ae_restrict_iff' sorry).mp
    (Filter.EventuallyEq.restrict this))]
  clear this
  rw [polarCoordToMixedSpace_source]
  rw [volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  simp_rw [lintegral_const_mul' _ _ sorry]
  simp_rw [← lintegral_indicator _ sorry]
  simp_rw [Set.indicator_indicator]
  simp_rw [lintegral_indicator _ sorry]
  simp only [Pi.one_apply, lintegral_const, MeasurableSet.univ, restrict_apply, Set.univ_inter,
    one_mul]
  simp_rw [← mul_assoc]
  rw [lintegral_mul_const']
  rw [mul_comm]
  congr 1
  · sorry
  · rw [← lintegral_indicator, ← lintegral_indicator]
    congr with x
    rw [Set.indicator_mul_right, Set.indicator_indicator]
    sorry
    sorry
    sorry
  all_goals sorry

open Classical in
def box₁ : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

def box₂ : Set ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioc (-π) π

def box := (box₁ K) ×ˢ (box₂ K)

def normLessThanOnePlus : (Set (E K)) := (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}

theorem normLessThanOnePlus_eq_image :
    normLessThanOnePlus K  = mapToUnitsPowComplex K '' (box K) := by
  sorry

theorem closure_subset_closure :
    closure (normLessThanOnePlus K) ⊆ mapToUnitsPowComplex K '' (closure (box K)) := by
  refine closure_minimal ?_ ?_
  · rw [normLessThanOnePlus_eq_image]
    refine Set.image_mono ?_
    exact subset_closure
  · have t₁ : IsCompact (closure (box K)) := sorry
    have t₂ : ContinuousOn (mapToUnitsPowComplex K) (closure (box K)) := sorry
    have := t₁.image_of_continuousOn t₂
    exact IsCompact.isClosed this

-- NOT TRUE
-- theorem box_subset_source :
--     (box K) ⊆ (mapToUnitsPowComplex K).source := by
--   rw [box, box₁, box₂, mapToUnitsPowComplex_source]

theorem normLessThanOnePlus_subset_target :
    normLessThanOnePlus K ⊆ (mapToUnitsPowComplex K).target := sorry

theorem interior_eq_interior :
    mapToUnitsPowComplex K '' (interior (box K)) = interior (normLessThanOnePlus K) := by
  have : (mapToUnitsPowComplex K).IsImage (box K) (normLessThanOnePlus K) := sorry
  have := this.interior
  have := PartialHomeomorph.IsImage.image_eq this
  rwa [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr] at this
  · refine subset_trans ?_ (normLessThanOnePlus_subset_target K)
    exact interior_subset
  · rw [mapToUnitsPowComplex_source]
    sorry

open Classical in
example : volume (mapToUnitsPowComplex K '' (interior (box K))) =
    volume (mapToUnitsPowComplex K '' (closure (box K))) := by
  have : interior (box K) =
    (Set.univ.pi fun _ ↦ Set.Ioo 0 1) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := sorry
  rw [this]
  clear this
  have : closure (box K) = (Set.Icc 0 1) ×ˢ (Set.univ.pi fun _ ↦ Set.Icc (-π) π) := sorry
  rw [this]
  clear this
  rw [volume_mapToUnitsPowComplex_set_prod_set, volume_mapToUnitsPowComplex_set_prod_set]
  congr 1
  · simp_rw [volume_pi_pi, Real.volume_Ioo, Real.volume_Icc]
  · rw [setLIntegral_mapToUnitsPow, setLIntegral_mapToUnitsPow]
    congr 1
    refine setLIntegral_congr ?_
    rw [show (Set.univ.pi fun _ ↦ Set.Ioo (0 : ℝ) 1) = interior (Set.Icc 0 1) by
      simp_rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ, Pi.zero_apply, Pi.one_apply,
        interior_Icc]]
    exact interior_ae_eq_of_null_frontier ((convex_Icc _ _).addHaar_frontier volume)
    sorry
    sorry
    sorry
    sorry
  · sorry
  · sorry
  · sorry
  · sorry



#exit

---------

open Classical

local notation "F" K => (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)

local notation "G" K => ({w : InfinitePlace K // IsReal w} → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

@[simps! apply symm_apply source target]
def marcus₁ : PartialHomeomorph (F K) (F K) :=
  PartialHomeomorph.prod (mapToUnitsPow K) (PartialHomeomorph.refl _)

theorem marcus₁_image_prod (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    marcus₁ K '' (s ×ˢ t) = (mapToUnitsPow K '' s) ×ˢ t := by
  ext; aesop

@[simps apply symm_apply]
def marcus₂ : Homeomorph (F K) (G K) where
  toFun := fun x ↦ (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩)
  invFun := fun x ↦ ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩
  left_inv _ := by aesop
  right_inv _ := by
    simp_rw [dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]
  continuous_toFun := by dsimp only; fun_prop
  continuous_invFun := by
    dsimp only
    rw [continuous_prod_mk]
    refine ⟨?_, ?_⟩
    · rw [continuous_pi_iff]
      intro w
      by_cases hw : IsReal w
      · simp_rw [dif_pos hw]
        fun_prop
      · simp_rw [dif_neg hw]
        fun_prop
    · fun_prop

def marcus₂'_symm : (G K) ≃ᵐ (F K) := by
  refine MeasurableEquiv.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ _)) ?_
  refine MeasurableEquiv.trans MeasurableEquiv.prodAssoc.symm ?_
  refine MeasurableEquiv.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm))
    (MeasurableEquiv.refl _)))
    (MeasurableEquiv.refl _))
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm
    (MeasurableEquiv.refl _))

theorem volume_preserving_marcus₂_symm : MeasurePreserving (marcus₂ K).symm := by
  change MeasurePreserving (marcus₂'_symm K) volume volume
  exact MeasurePreserving.trans ((MeasurePreserving.id volume).prod
      (volume_preserving.arrowProdEquivProdArrow ℝ ℝ {w : InfinitePlace K // IsComplex w})) <|
    MeasurePreserving.trans (volume_preserving.prodAssoc.symm) <|
      MeasurePreserving.trans
        (((MeasurePreserving.id volume).prod (volume_preserving.arrowCongr' _
        (MeasurableEquiv.refl ℝ)
          (MeasurePreserving.id volume))).prod (MeasurePreserving.id volume))
      <| ((volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
        (fun w : InfinitePlace K ↦ IsReal w)).symm).prod (MeasurePreserving.id volume)

def marcus₃ : PartialHomeomorph (F K) (E K) :=
  (marcus₂ K).toPartialHomeomorph.trans <|
    (PartialHomeomorph.refl _).prod <| PartialHomeomorph.pi fun _ ↦ Complex.polarCoord.symm

@[simp]
theorem marcus₃_apply (x : F K) :
    marcus₃ K x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := by
  simp_rw [marcus₃, PartialHomeomorph.coe_trans, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, Function.comp_apply, id_eq,  Homeomorph.toPartialHomeomorph_apply,
    marcus₂_apply, PartialHomeomorph.pi, PartialHomeomorph.symm_toPartialEquiv,
    PartialHomeomorph.mk_coe, PartialEquiv.pi_apply, PartialHomeomorph.coe_coe_symm]

-- Probably merge with volume_marcus₃_set_prod_set
theorem lintegral_marcus₃ (f : (E K) → ENNReal) :
    ∫⁻ x, f x = ∫⁻ x, (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal) * f (marcus₃ K x) := by
  rw [← (volume_preserving_marcus₂_symm K).lintegral_comp]
  simp only [marcus₂_symm_apply, Subtype.coe_eta, ENNReal.coe_finset_prod, marcus₃_apply]
  simp_rw [dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]
  rw [volume_eq_prod, volume_eq_prod, lintegral_prod, lintegral_prod]
  congr with x
  dsimp only
  all_goals sorry

@[simp]
theorem marcus₃_symm_apply (x : E K) :
    (marcus₃ K).symm x =
      ⟨fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else
        ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖, fun w ↦ Complex.arg (x.2 w)⟩ := by
  simp [marcus₃, Complex.polarCoord, Complex.abs_eq_sqrt_sq_add_sq]

theorem marcus₃_source : (marcus₃ K).source =
    (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [marcus₃]
  rw [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.prod_toPartialEquiv,
    PartialHomeomorph.refl_partialEquiv, PartialHomeomorph.pi_toPartialEquiv,
    PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source]
  rw [Homeomorph.toPartialHomeomorph_source, PartialHomeomorph.toFun_eq_coe,
    Homeomorph.toPartialHomeomorph_apply, PartialEquiv.prod_source, PartialEquiv.refl_source]
  rw [PartialEquiv.pi_source, PartialEquiv.symm_source, Set.univ_inter]
  rw [marcus₂]
  simp
  rw [Set.mk_preimage_prod, Set.preimage_univ, Set.univ_inter]
  rw [Complex.polarCoord_target]
  ext
  simp [forall_and]

theorem marcus₃_target :
    (marcus₃ K).target = Set.univ ×ˢ Set.univ.pi fun _ ↦ Complex.slitPlane := by
  rw [marcus₃]
  simp [Complex.polarCoord_source]

def full_marcus : PartialHomeomorph (F K) (E K) := by
  refine PartialHomeomorph.trans (marcus₁ K) (marcus₃ K)

theorem full_marcus_source :
    (full_marcus K).source =
      (Set.univ.pi fun i ↦ if i = w₀ then Set.Ioi 0 else Set.univ) ×ˢ
        Set.univ.pi fun _ ↦ Set.Ioo (-π) π := by
  simp only [full_marcus, PartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
    marcus₁_source, PartialHomeomorph.toFun_eq_coe]
  let U : Set ℝ := if ∃ w : InfinitePlace K, IsComplex w then {0}ᶜ else Set.univ
  have : (marcus₁ K) ⁻¹' (marcus₃ K).source =
      (Set.univ.pi fun w ↦ if w = w₀ then U else Set.univ) ×ˢ
        (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
    ext x
    simp_rw [marcus₃_source, Set.mem_preimage, marcus₁_apply, Set.mem_prod, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_ite_univ_left, not_isReal_iff_isComplex,
      and_congr_left_iff, Set.mem_ite_univ_right, Set.mem_Ioi, lt_iff_le_and_ne,
      mapToUnitsPow_nonneg, true_and, ne_comm (a := (0:ℝ)), ne_eq, mapToUnitsPow_zero_iff]
    simp_rw [forall_eq]
    intro _
    dsimp only [U]
    by_cases hc : ∃ w : InfinitePlace K, IsComplex w
    · obtain ⟨w, hw⟩ := hc
      have : (∀ (z : InfinitePlace K), z.IsComplex → ¬ x.1 w₀ = 0) ↔ x.1 w₀ ≠ 0 :=
        ⟨fun h ↦ h w hw, fun h _ _ ↦ h⟩
      rw [this, if_pos, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨w, hw⟩
    · have : (∀ (z : InfinitePlace K), z.IsComplex → ¬ x.1 w₀ = 0) := by
        rw [not_exists] at hc
        exact fun z a _ ↦ hc z a
      simp [this]
  rw [this]
  rw [Set.prod_inter_prod, Set.univ_inter]
  rw [← Set.pi_inter_distrib]
  congr! 3
  dsimp only [U]
  split_ifs <;> aesop

theorem full_marcus_target :
    (full_marcus K).target =
      (Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Complex.slitPlane) := by
  simp_rw [full_marcus, PartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_target,
    marcus₃_target, PartialHomeomorph.coe_coe_symm, marcus₁_target]
  have : (marcus₃ K).symm ⁻¹' (Set.univ.pi fun x ↦ Set.Ioi 0) ×ˢ Set.univ =
      (Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ {0}ᶜ) := by
    ext
    simp_rw [Set.mem_preimage, marcus₃_symm_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      true_implies, and_true, Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff]
    refine ⟨fun h ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun h w ↦ ?_⟩
    · have := h w
      rwa [dif_pos w.prop] at this
    · have := h w
      rwa [dif_neg (not_isReal_iff_isComplex.mpr w.prop), norm_pos_iff] at this
    · by_cases hw : IsReal w
      · rw [dif_pos hw]
        exact h.1 ⟨w, hw⟩
      · rw [dif_neg hw, norm_pos_iff]
        exact h.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩
  rw [this, Set.prod_inter_prod, Set.univ_inter]
  rw [← Set.pi_inter_distrib]
  have : Complex.slitPlane ∩ {0}ᶜ = Complex.slitPlane := by simp
  simp_rw [this]

def normVector : (E K) → (InfinitePlace K → ℝ) := fun x w ↦ normAtPlace w x

theorem normVector_full_marcus_apply (x : F K) :
    normVector K (full_marcus K x) = mapToUnitsPow K x.1 := by
  unfold  normVector
  simp [full_marcus, marcus₃]
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_isReal hw]
    simp
    sorry
  · rw [normAtPlace_apply_isComplex hw]
    simp [PartialHomeomorph.pi_apply, Complex.polarCoord_symm_abs]
    sorry

theorem marcus₃_prod_pi (s : Set (InfinitePlace K → ℝ)) (hs₁ : ∀ x, x ∈ s ↔ (fun w ↦ ‖x w‖) ∈ s) :
    marcus₃ K '' (s ×ˢ Set.univ.pi fun _ ↦ Set.Ioc (-π) π) =
      {x : E K | (fun w ↦ normAtPlace w x) ∈ s} := by
  ext x
  simp_rw [marcus₃_apply]
  simp_rw [Set.mem_image, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, ⟨hy₁, _⟩, rfl⟩ := h
    refine Set.mem_setOf.mpr ?_
    have := (hs₁ y.1).mp hy₁
    convert this with w
    obtain hw | hw := isReal_or_isComplex w
    · rw [normAtPlace_apply_isReal hw]
    · rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.polarCoord_symm_abs,
        Real.norm_eq_abs]
  · refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      exact fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else
        ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
      exact fun w ↦ Complex.arg (x.2 w)
    · rw [hs₁]
      convert_to (fun w ↦ normAtPlace w x) ∈ s
      · ext w
        by_cases hw : IsReal w
        · simp_rw [dif_pos hw, normAtPlace_apply_isReal hw]
        · simp_rw [dif_neg hw, norm_norm,
            normAtPlace_apply_isComplex (not_isReal_iff_isComplex.mp hw)]
      · exact h
    · exact fun w ↦ Complex.arg_mem_Ioc (x.2 w)
    · ext w
      · simp_rw [dif_pos w.prop]
      · simp [dif_neg (not_isReal_iff_isComplex.mpr w.prop), normAtPlace_apply_isComplex w.prop]

theorem image_by_marcus₃ (s : Set (E K)) (h₁ : ∀ x ∈ s, ∀ w, 0 ≤ x.1 w)
    (h₂ : ∀ x, x ∈ s ↔ ⟨fun w ↦ x.1 w, fun w ↦ ‖x.2 w‖⟩ ∈ s) :
    s = marcus₃ K '' ((normVector K '' s) ×ˢ Set.univ.pi fun _ ↦ Set.Ioc (-π) π) := by
  rw [marcus₃_prod_pi]
  sorry
  sorry

def box₁ : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

def box₂ : Set ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioc (-π) π

def box : Set (F K) := (box₁ K) ×ˢ (box₂ K)

def normLessThanOnePlus : (Set (E K)) := (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}

theorem eval₀ :
    mapToUnitsPow K '' (box₁ K) = normVector K '' (normLessThanOnePlus K ) := sorry

theorem normLessThanOnePlus_eq_image :
    normLessThanOnePlus K  = full_marcus K '' (box K) := by
  unfold full_marcus box
  simp_rw [PartialHomeomorph.coe_trans, Set.image_comp, marcus₁_image_prod]
  rw [box₂, eval₀]
  convert (image_by_marcus₃ K (normLessThanOnePlus K) ?_ ?_).symm
  · sorry
  · sorry
  · sorry
  · sorry

-- open ENNReal in
-- private theorem volume_marcus₃_set_prod_set_aux
--     (f : (InfinitePlace K → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ) → ℝ≥0∞)
--     (W : Finset {w : InfinitePlace K // w.IsComplex}) (hf : Measurable f)
--     (a : {w : InfinitePlace K // w.IsComplex} → ℂ) (x : {w : InfinitePlace K // w.IsReal} → ℝ) :
--     (∫⋯∫⁻_W, fun y ↦ f ⟨x, fun w ↦ ‖y w‖⟩ ∂fun _ ↦ (volume : Measure ℂ)) a =
--       (2 * NNReal.pi) ^ W.card * (∫⋯∫⁻_W, (fun y ↦ (∏ i ∈ W, (y i).toNNReal) * f ⟨x, y⟩)
--         ∂fun _ ↦ (volume.restrict (Set.Ici (0 : ℝ)))) (fun i ↦ ‖a i‖) := by
--   sorry

-- example (s : Set (InfinitePlace K → ℝ)) (t : {w : InfinitePlace K // IsComplex w} → Set ℝ)
--     (W : Finset {w : InfinitePlace K // w.IsComplex}) (a : {w : InfinitePlace K // IsComplex w} → ℂ)
--     (x : {w : InfinitePlace K // IsReal w} → ℝ) :
--     (∫⋯∫⁻_W, fun y ↦ (s ×ˢ Set.univ.pi fun w ↦ t w).indicator 1 (x, y)
--       ∂fun _ ↦ (volume : Measure ℂ)) a = ∏ w ∈ W, volume (t w) * ∫⁻ a, s.indicator 1 a := sorry



-- Prove the full_marcus version below instead?
theorem volume_marcus₃_set_prod_set (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
   -- (t : {w : InfinitePlace K // IsComplex w} → Set ℝ) :
--    volume (marcus₃ K '' (s ×ˢ (Set.univ.pi fun w ↦ t w))) = ∏ w, volume (t w) *
    volume (marcus₃ K '' s ×ˢ t) = volume t *
      ∫⁻ x in s, ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator]
  rw [lintegral_marcus₃]
  simp_rw [Set.indicator_image sorry]
  rw [Measure.volume_eq_prod, lintegral_prod]
  simp_rw [show (fun _ ↦ (1 : ℝ≥0∞)) ∘ (marcus₃ K) = fun _ ↦ 1 by aesop]
  have : ∀ x y,
    (s ×ˢ t).indicator (fun x ↦ (1 : ℝ≥0∞)) (x, y) = (s.indicator 1 x) * (t.indicator 1 y) := by
      intro x y
      exact Set.indicator_prod_one
  simp_rw [this]
  simp_rw [lintegral_const_mul' _ _ sorry]
  simp_rw [lintegral_indicator _ sorry, Pi.one_apply, setLIntegral_one, ← mul_assoc]
  rw [lintegral_mul_const', mul_comm]
  rw [← lintegral_indicator]
  congr
  ext

  all_goals sorry

theorem volume_full_marcus_set_prod_set (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    volume (full_marcus K '' (s ×ˢ t)) =
    volume t * ∫⁻ x in mapToUnitsPow K '' s,
      ∏ w : { w : InfinitePlace K // w.IsComplex }, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator, Measure.volume_eq_prod, lintegral_prod]
  rw [full_marcus, PartialHomeomorph.coe_trans, Set.image_comp, marcus₁_image_prod]
  rw [marcus₃]
  simp only [PartialHomeomorph.coe_trans, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Homeomorph.toPartialHomeomorph_apply, Function.comp_apply,
    marcus₂_apply]
  all_goals sorry



-- theorem volume_normLessThanOnePlus :
--     (volume (normLessThanOnePlus K)).toReal = π ^ NrComplexPlaces K * regulator K := by
--   rw [normLessThanOnePlus_eq_image, box, volume_full_marcus_set_prod_set]
--   rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume sorry
--      (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_mapToUnitsPow K c))
--      (injOn_mapToUnitsPow K)]
--   simp_rw [jacobian_det]
--   sorry

theorem lintegral_mapToUnitsPow (s : Set (InfinitePlace K → ℝ)) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (mapToUnitsPow K) '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * ENNReal.ofReal (regulator K) * (finrank ℚ K) *
      ∫⁻ x in s,
          ENNReal.ofReal (∏ i : {w : InfinitePlace K // IsComplex w}, (mapToUnitsPow K x i))⁻¹ *
        ENNReal.ofReal |x w₀| ^ rank K * f (mapToUnitsPow K x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume sorry
     (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_mapToUnitsPow K c))
     sorry]
  simp_rw [jacobian_det]
  rw [← lintegral_const_mul']
  congr with x
  rw [ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul, ENNReal.ofReal_mul,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow, ENNReal.ofReal_pow]
  rw [ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  ring_nf
  · positivity
  · positivity
  · rw [inv_nonneg]
    exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
  · refine mul_nonneg ?_ ?_
    · rw [inv_nonneg]
      exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
    · positivity
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · rw [inv_nonneg]
      exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
    · positivity
    · positivity
  · refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · rw [inv_nonneg]
      exact Finset.prod_nonneg fun _ _ ↦ mapToUnitsPow_nonneg K _ _
    · positivity
    · positivity
    · positivity
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_
    · refine ENNReal.pow_ne_top ?_
      rw [ENNReal.inv_ne_top]
      exact two_ne_zero
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.natCast_ne_top _

theorem closure_subset_closure :
    closure (normLessThanOnePlus K) ⊆ full_marcus K '' (closure (box K)) := by
  refine closure_minimal ?_ ?_
  · rw [normLessThanOnePlus_eq_image]
    refine Set.image_mono ?_
    exact subset_closure
  · have t₁ : IsCompact (closure (box K)) := sorry
    have t₂ : ContinuousOn (full_marcus K) (closure (box K)) := sorry
    have := t₁.image_of_continuousOn t₂
    exact IsCompact.isClosed this

theorem box_subset_source :
    (box K) ⊆ (full_marcus K).source := sorry

theorem normLessThanOnePlus_subset_target :
    normLessThanOnePlus K ⊆ (full_marcus K).target := sorry

theorem interior_eq_interior :
    full_marcus K '' (interior (box K)) = interior (normLessThanOnePlus K) := by
  have : (full_marcus K).IsImage (box K) (normLessThanOnePlus K) := sorry
  have := this.interior
  have := PartialHomeomorph.IsImage.image_eq this
  rwa [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr] at this
  · refine subset_trans ?_ (normLessThanOnePlus_subset_target K)
    exact interior_subset
  · refine subset_trans ?_ (box_subset_source K)
    exact interior_subset

example : volume (full_marcus K '' (interior (box K))) =
    volume (full_marcus K '' (closure (box K))) := by
  have : interior (box K) =
    (Set.univ.pi fun _ ↦ Set.Ioo 0 1) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := sorry
  rw [this]
  clear this
  have : closure (box K) = (Set.Icc 0 1) ×ˢ (Set.univ.pi fun _ ↦ Set.Icc (-π) π) := sorry
  rw [this]
  clear this
  rw [volume_full_marcus_set_prod_set, volume_full_marcus_set_prod_set]
  congr 1
  · simp_rw [volume_pi_pi, Real.volume_Ioo, Real.volume_Icc]
  · rw [lintegral_mapToUnitsPow, lintegral_mapToUnitsPow]
    congr 1
    refine setLIntegral_congr ?_
    rw [show (Set.univ.pi fun _ ↦ Set.Ioo (0 : ℝ) 1) = interior (Set.Icc 0 1) by
      simp_rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ, Pi.zero_apply, Pi.one_apply,
        interior_Icc]]
    exact interior_ae_eq_of_null_frontier ((convex_Icc _ _).addHaar_frontier volume)

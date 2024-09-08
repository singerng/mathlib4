/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.RingTheory.Ideal.IsPrincipal

import Mathlib.Sandbox

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`. The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂`
that is a fundamental domain for the action of `(𝓞 K)ˣ` up to roots of unity.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for
`u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset stable
by multiplication by a real number, see `smul_mem_of_mem`--, that is also a fundamental domain
for the action of `(𝓞 K)ˣ` up to roots of unity, see `exists_unitSMul_me` and
`torsion_unitSMul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPoint`: the subset of elements of the
fundamental cone that are images of algebraic integers of `K`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPointEquiv`: the equivalence between
`fundamentalCone.integralPoint K` and the principal non-zero ideals of `𝓞 K` times the
torsion of `K`.

* `NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_eq`: the number of principal
non-zero ideals in `𝓞 K` of norm `n` multiplied by the number of roots of unity is
equal to the number of `fundamentalCone.integralPoint K` of norm `n`.

## Tags

number field, canonical embedding, principal ideals
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by multiplication component
by component with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (E K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (E K) where
  one_smul := fun _ ↦ by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (E K) where
  smul_zero := fun _ ↦ by simp_rw [unitSMul_smul, mul_zero]

variable [NumberField K]

theorem unitSMul_eq_iff_mul_eq {x y : (𝓞 K)} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

theorem norm_unitSMul (u : (𝓞 K)ˣ) (x : E K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

theorem unitSMul_eq_zero (u : (𝓞 K)ˣ) (x : E K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · have := congr_fun (congr_arg Prod.fst h) w
      rw [unitSMul_smul, Prod.fst_mul, Pi.mul_apply, Prod.fst_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp only [mixedEmbedding_apply_ofIsReal, map_eq_zero,
        RingOfIntegers.coe_eq_zero_iff, Units.ne_zero, not_false_eq_true])
    · have := congr_fun (congr_arg Prod.snd h) w
      rw [unitSMul_smul, Prod.snd_mul, Pi.mul_apply, Prod.snd_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp only [mixedEmbedding_apply_ofIsComplex, map_eq_zero,
        RingOfIntegers.coe_eq_zero_iff, Units.ne_zero, not_false_eq_true])
  · rw [h, smul_zero]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional

variable [NumberField K] {K}

open Classical in
/-- The map from `ℝ^r₁ × ℂ^r₂` to `{w : InfinitePlace K // w ≠ w₀} → ℝ` (with `w₀` a fixed place)
defined in such way that: 1) it factors the map `logEmbedding`, see `logMap_eq_logEmbedding`;
2) it is constant on the lines `{c • x | c ∈ ℝ}`, see `logMap_smul`. -/
def logMap (x : E K) : {w : InfinitePlace K // w ≠ w₀} → ℝ := fun w ↦
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

theorem logMap_apply (x : E K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    logMap x w = mult w.val * (Real.log (normAtPlace w.val x) -
      Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹) := rfl

@[simp]
theorem logMap_zero : logMap (0 : E K) = 0 := by
  ext
  rw [logMap, map_zero, map_zero, Real.log_zero, zero_mul, sub_self, mul_zero, Pi.zero_apply]

@[simp]
theorem logMap_one : logMap (1 : E K) = 0 := by
  ext
  rw [logMap, map_one, show 1 = mixedEmbedding K (1 : (𝓞 K)ˣ) by
      rw [Units.val_one, map_one, map_one], norm_unit, Real.log_one, zero_mul, sub_self,
    mul_zero, Pi.zero_apply]

theorem logMap_mul {x y : E K} (hx : mixedEmbedding.norm x ≠ 0) (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  rw [map_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

theorem logMap_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {x : ι → (E K)}
    (hx : ∀ i ∈ s, mixedEmbedding.norm (x i) ≠ 0) :
    logMap (∏ i ∈ s, x i) = ∑ i ∈ s, logMap (x i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi h_ind =>
      rw [Finset.prod_cons, Finset.sum_cons, logMap_mul, h_ind]
      · exact fun _ h ↦ hx _ (Finset.mem_cons_of_mem h)
      · exact hx i (Finset.mem_cons_self i s)
      · rw [map_prod, Finset.prod_ne_zero_iff]
        exact fun _ h ↦ hx _ (Finset.mem_cons_of_mem h)

theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K u := by
  ext
  simp_rw [logMap, mixedEmbedding.norm_unit, Real.log_one, zero_mul, sub_zero, normAtPlace_apply,
    logEmbedding_component]

theorem logMap_unitSMul (u : (𝓞 K)ˣ) {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    logMap (u • x) = logEmbedding K u + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

theorem logMap_torsion_unitSMul (x : E K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

theorem logMap_smul {x : E K} (hx : mixedEmbedding.norm x ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, logMap_mul _ hx, add_left_eq_self]
  · ext
    have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
    simp_rw [logMap, normAtPlace_real, norm_real, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
      sub_self, zero_mul, Pi.zero_apply]
  · rw [norm_real]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)

theorem measurable_logMap :
    Measurable (logMap : (E K) → _) :=
  measurable_pi_iff.mpr fun _ ↦
    measurable_const.mul <| (continuous_normAtPlace _).measurable.log.sub
      <| (mixedEmbedding.continuous_norm K).measurable.log.mul measurable_const

theorem continuousOn_logMap :
    ContinuousOn (logMap : (E K) → _) {x | mixedEmbedding.norm x ≠ 0} := by
  refine continuousOn_pi.mpr fun w ↦ continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
  · exact Real.continuousOn_log.comp''  (continuous_normAtPlace _).continuousOn
      fun _ hx ↦ mixedEmbedding.norm_ne_zero_iff.mp hx _
  · exact ContinuousOn.mul
      (Real.continuousOn_log.comp''  (mixedEmbedding.continuous_norm K).continuousOn
        fun _ hx ↦ hx) continuousOn_const

theorem logMap_apply_of_norm_one {x : E K} (hx : mixedEmbedding.norm x = 1) {w : InfinitePlace K}
    (hw : w ≠ w₀) :
    logMap x ⟨w, hw⟩ = mult w * Real.log (normAtPlace w x) := by
  rw [logMap, hx, Real.log_one, zero_mul, sub_zero]

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem nonZeroDivisors BigOperators

variable [NumberField K]

open Classical in
/-- The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed by multiplication by
a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the action of `(𝓞 K)ˣ` up
to roots of unity, see `exists_unitSMul_mem` and `torsion_unitSMul_mem_of_mem`. -/
def fundamentalCone : Set (E K) :=
  logMap⁻¹' (Zspan.fundamentalDomain ((basisUnitLattice K).ofZlatticeBasis ℝ _)) \
    {x | mixedEmbedding.norm x = 0}

namespace fundamentalCone

variable {K}

-- Use this to golf some proofs? (or remove it)
open Classical in
theorem mem_fundamentalCone {x : E K} :
    x ∈ fundamentalCone K ↔
      logMap x ∈ Zspan.fundamentalDomain ((basisUnitLattice K).ofZlatticeBasis ℝ _) ∧
      mixedEmbedding.norm x ≠ 0 := by
  rw [fundamentalCone, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq]

theorem norm_pos_of_mem {x : E K} (hx : x ∈ fundamentalCone K) :
    0 < mixedEmbedding.norm x :=
  lt_iff_le_and_ne.mpr ⟨mixedEmbedding.norm_nonneg _, Ne.symm hx.2⟩

theorem normAtPlace_pos_of_mem {x : E K} (hx : x ∈ fundamentalCone K) (w : InfinitePlace K) :
    0 < normAtPlace w x :=
  lt_iff_le_and_ne.mpr ⟨normAtPlace_nonneg _ _,
    (mixedEmbedding.norm_ne_zero_iff.mp (ne_of_gt (norm_pos_of_mem hx)) w).symm⟩

theorem mem_of_normAtPlace_eq {x y : E K} (hx : x ∈ fundamentalCone K)
    (hy : ∀ w, normAtPlace w y = normAtPlace w x) :
    y ∈ fundamentalCone K := by
  have h₁ : mixedEmbedding.norm y = mixedEmbedding.norm x := by
    simp_rw [mixedEmbedding.norm_apply, hy]
  have h₂ : logMap y = logMap x := by
    ext
    simp_rw [logMap, hy, h₁]
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, h₂]
    exact hx.1
  · rw [Set.mem_setOf_eq, h₁]
    exact hx.2

theorem smul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_setOf_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

theorem smul_mem_iff_mem {x : E K} {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_of_mem h hc⟩
  convert smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

theorem exists_unitSMul_mem {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (basisUnitLattice K).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unitSMul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_unitSMul_mem_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ}
    (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_torsion_unitSMul _ hζ]
    exact hx.1
  · simpa only [unitSMul_smul, Set.mem_setOf_eq, map_mul, norm_eq_norm, Rat.cast_abs, mul_eq_zero,
    abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff, RingOfIntegers.coe_eq_zero_iff,
    Units.ne_zero, false_or] using hx.2

theorem unitSMul_mem_iff_mem_torsion {x : E K} (hx : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← logEmbedding_eq_zero_iff]
    let B := (basisUnitLattice K).ofZlatticeBasis ℝ
    refine (Subtype.mk_eq_mk (h := ?_) (h' := ?_)).mp <|
      ExistsUnique.unique (Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)) ?_ ?_
    · change logEmbedding K u ∈ (Submodule.span ℤ (Set.range B)).toAddSubgroup
      rw [Basis.ofZlatticeBasis_span ℝ (unitLattice K)]
      exact ⟨u, trivial, rfl⟩
    · exact Submodule.zero_mem _
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unitSMul _ hx.2]
      exact h.1
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      exact hx.1
  · exact torsion_unitSMul_mem_of_mem hx h

variable (K) in
theorem measurableSet :
    MeasurableSet (fundamentalCone K) := by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
    refine MeasurableSet.preimage (Zspan.fundamentalDomain_measurableSet _) <|
      measurable_pi_iff.mpr fun w ↦ measurable_const.mul ?_
    exact (continuous_normAtPlace _).measurable.log.sub <|
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

section normLessOne

variable (K)

def normLessThanOne : Set (E K) := {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

abbrev normEqOne : Set (E K) := {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x = 1}

variable {K} in
theorem mem_normLessThanOne_of_normAtPlace_eq {x y : E K} (hx : x ∈ normLessThanOne K)
    (hy : ∀ w, normAtPlace w y = normAtPlace w x) :
    y ∈ normLessThanOne K := by
  have h₁ : mixedEmbedding.norm y = mixedEmbedding.norm x := by
    simp_rw [mixedEmbedding.norm_apply, hy]
  exact ⟨mem_of_normAtPlace_eq hx.1 hy, h₁ ▸ hx.2⟩

theorem mem_normEqOne_of_normAtPlace_eq {x y : E K} (hx : x ∈ normEqOne K)
    (hy : ∀ w, normAtPlace w y = normAtPlace w x) :
    y ∈ normEqOne K := by
  have h₁ : mixedEmbedding.norm y = mixedEmbedding.norm x := by
    simp_rw [mixedEmbedding.norm_apply, hy]
  exact ⟨mem_of_normAtPlace_eq hx.1 hy, h₁ ▸ hx.2⟩

open Pointwise FiniteDimensional Bornology MeasureTheory Filter

theorem smul_normEqOne {c : ℝ} (hc : 0 < c) :
    c • normEqOne K = {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x = c ^ finrank ℚ K} := by
  ext
  rw [← Set.preimage_smul_inv₀ (ne_of_gt hc), Set.preimage_setOf_eq, Set.mem_setOf_eq,
    mixedEmbedding.norm_smul, abs_inv, abs_eq_self.mpr hc.le, inv_pow, mul_comm, mul_inv_eq_one₀
    (pow_ne_zero _ (ne_of_gt hc)), Set.mem_setOf_eq, and_congr_left_iff]
  exact fun _ ↦ smul_mem_iff_mem (inv_ne_zero (ne_of_gt hc))

-- Use this to golf some proof before?
-- Use norm_norm_rpow_smul_eq_one
variable {K} in
theorem exists_mem_smul_normEqOne {x : E K} (hx : x ∈ normLessThanOne K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ x ∈ c • normEqOne K := by
  have h₁ : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  have h₂ : 0 < mixedEmbedding.norm x ^ (finrank ℚ K : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (norm_pos_of_mem hx.1) _
  refine ⟨(mixedEmbedding.norm x) ^ (finrank ℚ K : ℝ)⁻¹, h₂, ?_, ?_⟩
  · exact Real.rpow_le_one (mixedEmbedding.norm_nonneg _) hx.2 (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [smul_normEqOne K h₂]
    refine ⟨hx.1, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (mixedEmbedding.norm_nonneg _), inv_mul_cancel₀ h₁,
      Real.rpow_one]

-- Replace with Set.Ioc?
-- This is useless after the next result?
theorem smul_normEqOne_subset {c : ℝ} (hc₁ : 0 < c) (hc₂ : c ≤ 1) :
    c • normEqOne K ⊆ normLessThanOne K := by
  rw [smul_normEqOne K hc₁]
  refine fun x hx ↦ ⟨hx.1, ?_⟩
  rw [hx.2]
  exact pow_le_one _ hc₁.le hc₂

theorem normLessThanOne_eq_union_smul_normEqOne :
    normLessThanOne K = ⋃ c ∈ Set.Ioc (0 : ℝ) 1, c • normEqOne K := by
  ext
  simp_rw [Set.mem_iUnion, Set.mem_Ioc, exists_prop, and_assoc]
  exact ⟨fun hx ↦ exists_mem_smul_normEqOne hx,
    fun ⟨_, h₁, h₂, hx⟩ ↦ smul_normEqOne_subset K h₁ h₂ hx⟩

theorem smul_normLessThanOne_subset {c : ℝ} (hc₁ : c ≠ 0) (hc₂ : |c| ≤ 1) :
    c • normLessThanOne K ⊆ normLessThanOne K := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · refine smul_mem_of_mem hx.1 hc₁
  · rw [norm_smul]
    refine mul_le_one ?_ (mixedEmbedding.norm_nonneg x) hx.2
    exact pow_le_one _ (abs_nonneg c) hc₂

theorem isBounded_normEqOne :
    IsBounded (normEqOne K) := by
  classical
  let B := (basisUnitLattice K).ofZlatticeBasis ℝ
  obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_closedBall_lt 0 0
  have h₁ : ∀ ⦃x w⦄, x ∈ normEqOne K → w ≠ w₀ → |mult w * Real.log (normAtPlace w x)| ≤ r := by
    intro x w hx hw
    rw [← logMap_apply_of_norm_one hx.2]
    suffices ‖logMap x‖ ≤ r by exact (pi_norm_le_iff_of_nonneg hr₁.le).mp this ⟨w, hw⟩
    exact mem_closedBall_zero_iff.mp (hr₂ hx.1.1)
  have h₂ : ∀ ⦃x⦄, x ∈ normEqOne K → mult (w₀ : InfinitePlace K) * Real.log (normAtPlace w₀ x) ≤
      (Finset.univ.erase (w₀ : InfinitePlace K)).card • r := by
    intro x hx
    suffices mult (w₀ : InfinitePlace K) * Real.log (normAtPlace w₀ x) =
        - ∑ w ∈ Finset.univ.erase w₀, mult w * Real.log (normAtPlace w x) by
      rw [this, ← Finset.sum_neg_distrib, ← Finset.sum_const]
      exact Finset.sum_le_sum fun w hw ↦
        neg_le_of_neg_le (abs_le.mp (h₁ hx (Finset.mem_erase.mp hw).1)).1
    simp_rw [← Real.log_pow]
    rw [← add_eq_zero_iff_eq_neg, Finset.univ.add_sum_erase (fun w ↦
      ((normAtPlace w x) ^ mult w).log) (Finset.mem_univ w₀), ← Real.log_prod,
      ← mixedEmbedding.norm_apply, hx.2, Real.log_one]
    exact fun w _ ↦  pow_ne_zero _ <| ne_of_gt (normAtPlace_pos_of_mem hx.1 w)
  have h₃ : ∀ ⦃x w c⦄, 0 ≤ c → x ∈ fundamentalCone K →
      mult w * Real.log (normAtPlace w x) ≤ c → normAtPlace w x ≤ Real.exp c := by
    intro x w c hc hx
    rw [← le_div_iff₀' (Nat.cast_pos.mpr mult_pos),
      Real.log_le_iff_le_exp (normAtPlace_pos_of_mem hx w)]
    exact fun h ↦ le_trans h <| Real.exp_le_exp.mpr (div_le_self hc one_le_mult)
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr
    ⟨max (Real.exp r) (Real.exp ((Finset.univ.erase (w₀ : InfinitePlace K)).card • r)),
      fun x hx ↦ mem_closedBall_zero_iff.mpr ?_⟩
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ ↦ ?_
  by_cases hw : w = w₀
  · rw [hw]
    exact (h₃ (nsmul_nonneg (hr₁.le) _) hx.1 (h₂ hx)).trans (le_max_right _ _)
  · exact le_trans (h₃ hr₁.le hx.1 (abs_le.mp (h₁ hx hw)).2) (le_max_left _ _)

theorem isBounded_normLessThanOne :
    IsBounded (normLessThanOne K) := by
  classical
  obtain ⟨r, hr₁, hr₂⟩ := (isBounded_normEqOne K).subset_ball_lt 0 0
  refine (Metric.isBounded_iff_subset_ball 0).mpr ⟨r, fun x hx ↦ ?_⟩
  obtain ⟨c, hc₁, _, hc₂⟩ := exists_mem_smul_normEqOne hx
  suffices x ∈ c • Metric.ball (0 : (E K)) r by
    rw [smul_ball (ne_of_gt hc₁), smul_zero] at this
    refine Set.mem_of_subset_of_mem (Metric.ball_subset_ball ?_) this
    rwa [mul_le_iff_le_one_left hr₁, Real.norm_eq_abs, abs_eq_self.mpr hc₁.le]
  exact (Set.image_subset _ hr₂) hc₂

theorem measurableSet_normEqOne :
    MeasurableSet (normEqOne K) :=
  MeasurableSet.inter (measurableSet K) <|
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem measurableSet_normLessThanOne :
    MeasurableSet (normLessThanOne K) :=
  MeasurableSet.inter (measurableSet K) <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

end normLessOne

variable (K) in
/-- The set of images by `mixedEmbedding` of algebraic integers of `K` contained in the
fundamental cone. -/
def integralPoint : Set (E K) :=
  fundamentalCone K ∩ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))

theorem exists_unique_preimage_of_integralPoint {x : E K} (hx : x ∈ integralPoint K) :
    ∃! a : (𝓞 K), mixedEmbedding K a = x := by
  refine ⟨hx.2.choose_spec.1.choose, ?_, fun _ h ↦ ?_⟩
  · convert hx.2.choose_spec.2
    exact hx.2.choose_spec.1.choose_spec
  · rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, h]
    convert hx.2.choose_spec.2.symm
    exact hx.2.choose_spec.1.choose_spec

theorem integralPoint_ne_zero (a : integralPoint K) :
    (a : E K) ≠ 0 := by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

/-- For `a : fundamentalCone K`, the unique non-zero algebraic integer which image by
`mixedEmbedding` is equal to `a`. -/
def preimageOfIntegralPoint (a : integralPoint K) : (𝓞 K)⁰ :=
  ⟨a.prop.2.choose_spec.1.choose, by
    simp_rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, RingOfIntegers.ext_iff,
      a.prop.2.choose_spec.1.choose_spec, ← (mixedEmbedding_injective K).eq_iff, map_zero,
      a.prop.2.choose_spec.2, integralPoint_ne_zero a, not_false_eq_true]⟩

@[simp]
theorem mixedEmbedding_preimageOfIntegralPoint (a : integralPoint K) :
    mixedEmbedding K (preimageOfIntegralPoint a : 𝓞 K) = (a : E K) := by
  rw [RingOfIntegers.coe_eq_algebraMap, ← a.prop.2.choose_spec.2, preimageOfIntegralPoint,
    a.prop.2.choose_spec.1.choose_spec]

theorem preimageOfIntegralPoint_mixedEmbedding {x : (𝓞 K)⁰}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ integralPoint K) :
    preimageOfIntegralPoint (⟨mixedEmbedding K (x : 𝓞 K), hx⟩) = x := by
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfIntegralPoint]

theorem exists_unitSMul_mem_integralPoint {x : E K} (hx : x ≠ 0)
    (hx' : x ∈ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integralPoint K := by
  replace hx : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unitSMul_mem hx
  obtain ⟨_, ⟨⟨x, rfl⟩, ⟨_, rfl⟩⟩⟩ := hx'
  exact ⟨u, hu, (u * x : K), ⟨u * x, rfl⟩, by simp_rw [unitSMul_smul, ← map_mul]⟩

theorem torsion_unitSMul_mem_integralPoint {x : E K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integralPoint K) :
    ζ • x ∈ integralPoint K := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx.2
  refine ⟨torsion_unitSMul_mem_of_mem hx.1 hζ, ⟨ζ * a, ?_, ?_⟩⟩
  · exact ⟨ζ * a, rfl⟩
  · rw [unitSMul_smul, map_mul]

variable (K) in
/-- The map that sends an element of `a : fundamentalCone K` to the associates class
of its preimage in `(𝓞 K)⁰`. By quotienting by the kernel of the map, which is equal to the group
of roots of unity, we get the equivalence `integralPointQuotEquivAssociates`. -/
def integralPointToAssociates (a : integralPoint K) : Associates (𝓞 K)⁰ :=
  ⟦preimageOfIntegralPoint a⟧

@[simp]
theorem integralPointToAssociates_apply (a : integralPoint K) :
    (integralPointToAssociates K a) = ⟦preimageOfIntegralPoint a⟧ := rfl

variable (K) in
theorem integralPointToAssociates_surjective :
    Function.Surjective (integralPointToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) ∈ integralPoint K := by
    refine exists_unitSMul_mem_integralPoint ?_  ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
    rw [map_ne_zero, RingOfIntegers.coe_ne_zero_iff]
    exact nonZeroDivisors.coe_ne_zero _
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfIntegralPoint,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]

@[simps]
instance integralPoint_torsionSMul: SMul (torsion K) (integralPoint K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x, torsion_unitSMul_mem_integralPoint hζ hx⟩

instance : MulAction (torsion K) (integralPoint K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integralPoint_torsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integralPoint_torsionSMul_smul_coe, Subgroup.coe_mul, mul_smul]

theorem integralPointToAssociates_eq_iff (a b : integralPoint K) :
    integralPointToAssociates K a = integralPointToAssociates K b ↔
      ∃ ζ : torsion K, ζ • a = b := by
  simp_rw [integralPointToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfIntegralPoint, integralPoint_torsionSMul_smul_coe]
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨⟨ζ, _⟩, h⟩ ↦ ?_⟩
  · refine ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simp [hu]⟩
    exact (unitSMul_mem_iff_mem_torsion a.prop.1 _).mp (by simp [hu, b.prop.1])
  · exact ⟨unitsNonZeroDivisorsEquiv.symm ζ, by simpa using h⟩

variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and
`Associates (𝓞 K)⁰`. -/
def integralPointQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃ Associates (𝓞 K)⁰ := by
  refine Equiv.ofBijective
    (Quotient.lift (integralPointToAssociates K)
      fun _ _ h ↦ ((integralPointToAssociates_eq_iff _ _).mpr h).symm)
    ⟨by
      convert Setoid.ker_lift_injective (integralPointToAssociates K)
      all_goals
      · ext a b
        rw [Setoid.ker_def, eq_comm, integralPointToAssociates_eq_iff b a,
          MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
      (Quot.surjective_lift _).mpr (integralPointToAssociates_surjective K)⟩

@[simp]
theorem integralPointQuotEquivAssociates_apply (a : integralPoint K) :
    integralPointQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfIntegralPoint a⟧ := rfl

theorem integralPoint_torsionSMul_stabilizer {a : integralPoint K} :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integralPoint_torsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfIntegralPoint, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

open Submodule Ideal

variable (K) in
def integralPointEquiv :
    integralPoint K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} × torsion K :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integralPoint K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integralPoint_torsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ ↦ (integralPointQuotEquivAssociates K).trans
        (Ideal.associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]
theorem integralPointEquiv_apply_fst (a : integralPoint K) :
    ((integralPointEquiv K a).1 : Ideal (𝓞 K)) = span {(preimageOfIntegralPoint a : 𝓞 K)} := by
  simp_rw [← associatesNonZeroDivisorsEquivIsPrincipal_apply,
    ← integralPointQuotEquivAssociates_apply]
  rfl

/-- The `mixedEmbedding.norm` of `a : integralPoint K` as a natural integer, see `intNorm_coe` . -/
def intNorm (a : integralPoint K) : ℕ := (Algebra.norm ℤ (preimageOfIntegralPoint a : 𝓞 K)).natAbs

@[simp]
theorem intNorm_coe (a : integralPoint K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : E K) := by
  rw [intNorm, Int.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
    ← norm_eq_norm, mixedEmbedding_preimageOfIntegralPoint]

theorem intNorm_le_iff (a : integralPoint K) (n : ℕ) :
    intNorm a ≤ n ↔ mixedEmbedding.norm (a : E K) ≤ n := by
  rw [← intNorm_coe, Nat.cast_le]

/-- The norm `intNorm` defined on `fundamentalCone.integralPoint K` lifts to a function
on the classes of `fundamentalCone.integralPoint K` modulo `torsion K`. -/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) → ℕ :=
  Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ by
    rw [← Nat.cast_inj (R := ℝ), intNorm_coe, intNorm_coe, ← hu, integralPoint_torsionSMul_smul_coe,
      norm_unitSMul]

@[simp]
theorem quotIntNorm_apply (a : integralPoint K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

variable (K) in
def integralPointEquivNorm (n : ℕ) :
    {a : integralPoint K // intNorm a = n} ≃
      {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc {a // intNorm a = n}
      ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      (Equiv.subtypeEquiv (integralPointEquiv K) fun _ ↦ by simp [intNorm, absNorm_span_singleton])
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K :=
      Equiv.prodSubtypeFstEquivSubtypeProd (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} ↦
        absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1) (fun I ↦ absNorm I.1 = n))

@[simp]
theorem integralPointEquivNorm_apply_fst {n : ℕ} {a : integralPoint K} (ha : intNorm a = n) :
    ((integralPointEquivNorm K n ⟨a, ha⟩).1 : Ideal (𝓞 K)) =
      span {(preimageOfIntegralPoint a : 𝓞 K)} := by
  simp_rw [← associatesNonZeroDivisorsEquivIsPrincipal_apply,
    ← integralPointQuotEquivAssociates_apply]
  rfl

variable (K)

/-- For `n` positive, the number of `fundamentalCone.integralPoint K` of
norm `n` is equal to the number of principal ideals in `𝓞 K` of norm `n` multiplied by the number
of roots of unity in `K`. -/
theorem card_isPrincipal_norm_eq (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a = n} := by
  rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  exact Nat.card_congr (integralPointEquivNorm K n).symm

theorem card_isPrincipal_norm_le (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) ≤ n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a ≤ n} := by
  rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic n) _
      (fun I ↦ ⟨absNorm (I.1 : Ideal (𝓞 K)), Finset.mem_Iic.mpr I.1.2.2⟩)
      (fun a ↦ ⟨intNorm a.1, Finset.mem_Iic.mpr a.2⟩) fun ⟨i, hi⟩ ↦ ?_
  simp_rw [Subtype.mk.injEq]
  calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 ≤ n} // absNorm I.1.1 = i}
          × torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 ≤ n) ∧ absNorm I.1 = i}
          × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
      (p := fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1 ∧ absNorm I.1 ≤ n)
      (q := fun I ↦ absNorm I.1 = i))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = i ∧ absNorm I.1 ≤ n}
          × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ by aesop)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = i} × torsion K :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ by
      rw [and_iff_left_of_imp (a := absNorm _ = _) fun h ↦ Finset.mem_Iic.mp (h ▸ hi)])
    _ ≃ {a : integralPoint K // intNorm a = i} := (integralPointEquivNorm K i).symm
    _ ≃ {a : {a : integralPoint K // intNorm a ≤ n} // intNorm a.1 = i} :=
      (Equiv.subtypeSubtypeEquivSubtype fun h ↦ Finset.mem_Iic.mp (h ▸ hi)).symm

end fundamentalCone

end

end NumberField.mixedEmbedding

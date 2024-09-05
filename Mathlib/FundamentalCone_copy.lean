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
      refine this.resolve_left (by simp)
    · have := congr_fun (congr_arg Prod.snd h) w
      rw [unitSMul_smul, Prod.snd_mul, Pi.mul_apply, Prod.snd_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp)
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
    rw [← le_div_iff' (Nat.cast_pos.mpr mult_pos),
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

theorem frontier_normLessThanOne :
    frontier (normLessThanOne K) ⊆ (frontier (fundamentalCone K) ∩ {x | mixedEmbedding.norm x ≤ 1})
      ∪ normEqOne K := by
  rw [show normLessThanOne K = fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ 1} by
    rw [normLessThanOne]; ext; simp]
  refine le_trans (frontier_inter_subset _ _) ?_
  intro x hx
  cases hx with
  | inl h =>
      left
      have : closure {x : E K | mixedEmbedding.norm x ≤ 1} = {x | mixedEmbedding.norm x ≤ 1} :=
        closure_le_eq (mixedEmbedding.continuous_norm K) continuous_const
      rwa [← this]
  | inr h =>
      have : frontier {x : E K | mixedEmbedding.norm x ≤ 1} = {x | mixedEmbedding.norm x = 1} := by
        refine frontier_le_eq_eq (mixedEmbedding.continuous_norm K) continuous_const ?_
        intro x hx
        refine frequently_iff_seq_forall.mpr ?_
        refine ⟨?_, ?_, ?_⟩
        have := exists_seq_strictAnti_tendsto (1 : ℝ)
        · intro n
          exact (exists_seq_strictAnti_tendsto (1 : ℝ)).choose n • x
        · rw [show nhds x = nhds ((1 : ℝ) • x) by norm_num]
          refine Tendsto.smul_const ?_ _
          exact (exists_seq_strictAnti_tendsto (1 : ℝ)).choose_spec.2.2
        · intro n
          rw [mixedEmbedding.norm_smul, ← hx, mul_one]
          refine one_lt_pow ?_ ?_
          · rw [lt_abs]
            left
            exact (exists_seq_strictAnti_tendsto (1 : ℝ)).choose_spec.2.1 _
          · refine ne_of_gt ?_
            exact finrank_pos
      rw [this] at h
      by_cases hx : x ∈ fundamentalCone K
      · right
        refine ⟨hx, h.2⟩
      · left
        have : x ∉ interior (fundamentalCone K) := by
          by_contra h
          exact hx <| interior_subset h
        exact ⟨⟨h.1, this⟩, by rw [Set.mem_setOf_eq, h.2]⟩

theorem measurableSet_normEqOne :
    MeasurableSet (normEqOne K) :=
  MeasurableSet.inter (measurableSet K) <|
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem measurableSet_normLessThanOne :
    MeasurableSet (normLessThanOne K) :=
  MeasurableSet.inter (measurableSet K) <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

-- To prove that the frontier of `X` is of measure zero?
-- MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero

variable {K}

theorem measurableSet_positiveAt (T : Finset {w : InfinitePlace K // w.IsReal}) :
    MeasurableSet {x : E K | ∀ w ∈ T, 0 < x.1 w} := by
  refine MeasurableSet.congr (s := ⋂ z ∈ T, {x | x.1 z > 0})
    (MeasurableSet.biInter (Set.to_countable _) fun z _ ↦ ?_) (by ext; simp)
  exact measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const <|
        (measurable_pi_apply _).comp measurable_fst

-- flipSignAt?
open Classical in
def signFlipAt (w : {w : InfinitePlace K // w.IsReal}) : (E K) ≃L[ℝ] (E K) :=
  ContinuousLinearEquiv.prod (ContinuousLinearEquiv.piCongrRight
    fun w' ↦ if w' = w then ContinuousLinearEquiv.neg _ else ContinuousLinearEquiv.refl _ _)
      (ContinuousLinearEquiv.refl ℝ _)

@[simp]
theorem signFlipAt_apply_of_isReal_eq (w : {w // w.IsReal}) (x : E K) :
    (signFlipAt w x).1 w = - x.1 w := by simp [signFlipAt]

theorem signFlipAt_apply_of_isReal_ne (w w' : {w // w.IsReal}) (x : E K) (h : w' ≠ w) :
    (signFlipAt w x).1 w' = x.1 w' := by simp [signFlipAt, h]

theorem signFlipAt_apply_of_isComplex (w : {w // w.IsReal}) (w' : {w // w.IsComplex}) (x : E K) :
    (signFlipAt w x).2 w' = x.2 w' := rfl

theorem normAtPlace_signFlipAt (w : {w // w.IsReal}) (w' : InfinitePlace K) (x : E K) :
    normAtPlace w' (signFlipAt w x)= normAtPlace w' x := by
  obtain hw'₁ | hw'₁ := isReal_or_isComplex w'
  · by_cases hw'₂ : w' = w
    · simp_rw [normAtPlace_apply_isReal hw'₁, hw'₂, signFlipAt_apply_of_isReal_eq, norm_neg]
    · have : ⟨w', hw'₁⟩ ≠ w := by exact Subtype.coe_ne_coe.mp hw'₂
      simp_rw [normAtPlace_apply_isReal hw'₁, signFlipAt_apply_of_isReal_ne _ _ _ this]
  · simp_rw [normAtPlace_apply_isComplex hw'₁, signFlipAt_apply_of_isComplex]

theorem norm_signFlipAt (w : {w // w.IsReal}) (x : E K) :
    mixedEmbedding.norm (signFlipAt w x) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_signFlipAt]

theorem logMap_signFlipAt (w : {w // w.IsReal}) (x : E K) :
    logMap (signFlipAt w x) = logMap x := by
  ext
  simp_rw [logMap_apply, normAtPlace_signFlipAt, norm_signFlipAt]

open Classical in
theorem volume_preserving_signFlipAt (w : {w : InfinitePlace K // w.IsReal}) :
    MeasurePreserving (signFlipAt w) := by
  refine MeasurePreserving.prod (volume_preserving_pi fun w ↦ ?_) ( MeasurePreserving.id _)
  dsimp only
  split_ifs
  exact Measure.measurePreserving_neg _
  exact MeasurePreserving.id _

theorem signFlipAt_preimage_normLessThanOne (w : {w : InfinitePlace K // w.IsReal}) :
    signFlipAt w ⁻¹' (normLessThanOne K) = normLessThanOne K := by
  ext
  simp_rw [normLessThanOne, Set.preimage_setOf_eq, Set.mem_setOf_eq, mem_fundamentalCone,
    norm_signFlipAt, logMap_signFlipAt]

open Classical in
theorem volume_eq_zero_at (w : {w : InfinitePlace K // w.IsReal}) :
    volume {x : E K | x.1 w = 0} = 0 := by
  let A : AffineSubspace ℝ (E K) := by
    refine Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x : E K | x.1 w = 0}, ?_⟩, rfl⟩ ?_)
    · intro x y hx hy
      rw [Set.mem_setOf_eq] at hx hy ⊢
      rw [Prod.fst_add, Pi.add_apply, hx, hy, zero_add]
    · intro c x hx
      rw [Set.mem_setOf_eq] at hx ⊢
      rw [Prod.smul_fst, Pi.smul_apply, hx, smul_zero]
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  have : 1 ∈ A := h ▸ Set.mem_univ _
  simp [A] at this

open Classical in
theorem volume_inter_positiveAt {s : Set (E K)} (hs₁ : MeasurableSet s)
    (T : Finset {w : InfinitePlace K // w.IsReal}) (hs₂ : ∀ w ∈ T, signFlipAt w ⁻¹' s = s) :
    volume s = 2 ^ Finset.card T * volume (s ∩ {x | ∀ w ∈ T, 0 < x.1 w}) := by
  induction T using Finset.induction with
  | empty => simp
  | @insert w T hw h_ind =>
      have h₁ : (s ∩ {x | ∀ z ∈ T, 0 < x.1 z} : Set (E K)) =ᵐ[volume]
          (s ∩ {x | x.1 w < 0} ∩ {x | ∀ z ∈ T, 0 < x.1 z} ∪
            s ∩ {x | 0 < x.1 w} ∩ {x | ∀ z ∈ T, 0 < x.1 z} : Set (E K)) := by
        rw [Set.inter_assoc, Set.inter_assoc, ← Set.inter_union_distrib_left,
          ← Set.union_inter_distrib_right, ← Set.inter_assoc]
        refine (ae_eq_set_inter (inter_ae_eq_left_of_ae_eq_univ ?_) (by rfl)).symm
        rw [show Set.univ = ({x : E K | x.1 w < 0} ∪ {x | 0 < x.1 w}) ∪ {x | x.1 w = 0} by
          ext x; simpa [lt_trichotomy (x.1 w) 0] using ne_or_eq (x.1 w) 0]
        exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr (volume_eq_zero_at w))).symm
      have h₂ : Disjoint (s ∩ {x | x.1 w < 0} ∩ {x | ∀ z ∈ T, 0 < x.1 z})
          (s ∩ {x | 0 < x.1 w} ∩ {x | ∀ z ∈ T, 0 < x.1 z} ) := by
        refine (((Disjoint.inter_left' _ ?_).inter_right' _).inter_right _).inter_left _
        rw [Set.disjoint_right]
        intro _ hx hx'
        rw [Set.mem_setOf_eq] at hx hx'
        exact lt_asymm hx hx'
      have h₃ : volume (s ∩ {x | x.1 w < 0} ∩ {x | ∀ z ∈ T, 0 < x.1 z}) =
          volume (s ∩ {x | 0 < x.1 w} ∩ {x | ∀ z ∈ T, 0 < x.1 z}) := by
        rw [← (volume_preserving_signFlipAt w).measure_preimage, Set.preimage_inter,
          Set.preimage_inter, hs₂ _ (Finset.mem_insert_self w T)]
        congr
        · ext; simp
        · ext
          simp_rw [Set.preimage_setOf_eq, Set.mem_setOf_eq]
          refine ⟨fun h z hz ↦ ?_, fun h z hz ↦ ?_⟩
          · specialize h z hz
            rwa [signFlipAt_apply_of_isReal_ne] at h
            exact ne_of_mem_of_not_mem hz hw
          · rw [signFlipAt_apply_of_isReal_ne]
            exact h z hz
            exact ne_of_mem_of_not_mem hz hw
        · refine MeasurableSet.inter (MeasurableSet.inter hs₁.nullMeasurableSet ?_) ?_
          · refine measurableSet_lt (g := fun _ ↦ (0 : ℝ)) ?_ measurable_const
            sorry
            -- exact (measurable_pi_apply _).comp measurable_fst
          · sorry
            -- exact measurableSet_positiveAt T
      rw [h_ind, measure_congr h₁, measure_union h₂, h₃, ← two_mul, ← mul_assoc, ← pow_succ,
        Finset.card_insert_of_not_mem hw]
      · simp_rw [Finset.mem_insert, forall_eq_or_imp, Set.setOf_and, Set.inter_assoc]
      · refine MeasurableSet.inter (MeasurableSet.inter hs₁ ?_) ?_
        · refine measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const ?_
          exact (measurable_pi_apply _).comp measurable_fst
        · exact measurableSet_positiveAt T
      exact fun w hw ↦  hs₂ w (Finset.mem_insert_of_mem hw)

open Classical in
theorem volume_normLessThanOne_step1 :
    volume (normLessThanOne K) = 2 ^ (NrRealPlaces K) *
      volume (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) := by
  convert volume_inter_positiveAt (measurableSet_normLessThanOne K) Finset.univ ?_
  · simp
  · intro w _
    exact signFlipAt_preimage_normLessThanOne w

open Classical in
theorem volume_closure_normLessThanOne_step1 :
    volume (closure (normLessThanOne K)) = 2 ^ (NrRealPlaces K) *
      volume (closure (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}) := by
  convert volume_inter_positiveAt ?_ Finset.univ ?_
  · simp
  · exact measurableSet_closure
  · intro w _
    rw [ContinuousLinearEquiv.preimage_closure, signFlipAt_preimage_normLessThanOne]

open Classical in
theorem volume_interior_normLessThanOne_step1 :
    volume (interior (normLessThanOne K)) = 2 ^ (NrRealPlaces K) *
      volume (interior (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}) := by
  convert volume_inter_positiveAt ?_ Finset.univ ?_
  · simp
  · exact measurableSet_interior
  · intro w _
    rw [ContinuousLinearEquiv.preimage_interior, signFlipAt_preimage_normLessThanOne]

#exit

variable (K) in
def realSpaceToMixedSpace : (InfinitePlace K → ℝ) →ₐ[ℝ] (E K) where
  toFun := fun x ↦ ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

variable (K) in
def mixedSpaceToRealSpace : (E K) →* (InfinitePlace K → ℝ) where
  toFun := fun x w ↦
    if hw : w.IsReal then x.1 ⟨w, hw⟩ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_one' := sorry
  map_mul' := sorry

theorem mixedSpaceToRealSpace_apply (x : E K) :
    mixedSpaceToRealSpace K x = fun w ↦
      if hw : w.IsReal then x.1 ⟨w, hw⟩ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖ := rfl

theorem realSpaceToMixedSpace_apply (x : InfinitePlace K → ℝ) :
    realSpaceToMixedSpace K x = ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩ := rfl

theorem mixedSpaceToRealSpaceToMixedSpace_apply (x : E K) :
    realSpaceToMixedSpace K (mixedSpaceToRealSpace K x) = ⟨fun w ↦ x.1 w, fun w ↦ ‖x.2 w‖⟩ := by
  simp_rw [mixedSpaceToRealSpace_apply, realSpaceToMixedSpace_apply, Subtype.coe_eta,
    dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]

example :
    (realSpaceToMixedSpace K ∘ mixedSpaceToRealSpace K)⁻¹'
      (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) = normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w} := by
  ext x
  simp only [Set.mem_preimage, Function.comp_apply, mixedSpaceToRealSpaceToMixedSpace_apply]
  have h_norm : ∀ w, normAtPlace w (fun w ↦ x.1 w, fun w ↦ ‖x.2 w‖) = normAtPlace w x := by
    intro w
    obtain hw | hw := isReal_or_isComplex w
    · simp_rw [normAtPlace_apply_isReal hw]
    · simp_rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.abs_ofReal,
        Complex.abs_abs]
  refine ⟨fun h ↦ ⟨?_, h.2⟩, fun h ↦ ⟨?_, h.2⟩⟩
  · refine mem_normLessThanOne_of_normAtPlace_eq h.1 ?_
    exact fun w ↦ (h_norm w).symm
  · exact mem_normLessThanOne_of_normAtPlace_eq h.1 h_norm

 ---- ABOVE HERE ----


variable (K) in
theorem measure_preserving_split :
  MeasurePreserving (fun x : InfinitePlace K → ℝ ↦
    (fun w : {w // w.IsReal} ↦ x w.val, fun w : {w // w.IsComplex} ↦ x w.val)) where
  measurable := (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _).prod_mk
    (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)
  map_eq := sorry

theorem volume_of_eq_preimage (s : Set (E K))
    (hs₀ : MeasurableSet s) (hs₁ : (realSpaceToMixedSpace K ∘ mixedSpaceToRealSpace K)⁻¹' s = s) :
    volume s = (2 * NNReal.pi) ^ NrComplexPlaces K *
      ∫⁻ x in realSpaceToMixedSpace K ⁻¹' s ∩ {x | ∀ w, IsComplex w → 0 < x w},
        (∏ w : {w // IsComplex w}, (x w.val).toNNReal) := by
  rw [← setLIntegral_one, ← lintegral_indicator _ hs₀, Measure.volume_eq_prod, lintegral_prod]
  nth_rewrite 1 [← hs₁]
  have := fun (x : {w : InfinitePlace K // w.IsReal} → ℝ)
    (y : {w : InfinitePlace K // w.IsComplex } → ℂ) ↦ Set.indicator_comp_right (s := s)
    (f := realSpaceToMixedSpace K ∘ mixedSpaceToRealSpace K) (g := fun _ ↦ (1 : ENNReal))
    (x := (x, y))
  have t₁ : (fun x ↦ (1 : ENNReal)) ∘ (realSpaceToMixedSpace K) ∘ (mixedSpaceToRealSpace K) =
      (fun x ↦ 1) := by rfl
  rw [t₁] at this
  simp_rw [this]
  clear this
  simp_rw [Function.comp_apply, mixedSpaceToRealSpaceToMixedSpace_apply]
  simp_rw [volume_pi, lintegral_eq_lmarginal_univ (0 : {w // IsComplex w} → ℂ)]
  have := fun x : {w : InfinitePlace K // w.IsReal} → ℝ ↦ multiple_step₀ (fun y : {w : InfinitePlace K // w.IsComplex} → ℝ  ↦ s.indicator (fun _ ↦ (1 : ENNReal))
          (fun w ↦ x w, fun w ↦ y w)) ?_ Finset.univ 0
  simp_rw [this]
  clear this
  simp_rw [ Pi.zero_apply, norm_zero, lmarginal_univ]
  rw [lintegral_const_mul]
  rw [lintegral_lintegral]
  · rw [← measure_restrict_pi_pi, Measure.restrict_prod_eq_univ_prod]
    rw [← lintegral_indicator, ← volume_pi, ← volume_pi, ← Measure.volume_eq_prod]
    rw [← MeasurePreserving.lintegral_comp (measure_preserving_split K)]
    rw [← lintegral_indicator]
    congr
    · ext x
      by_cases hx : x ∈ (realSpaceToMixedSpace K) ⁻¹' s ∩ {x | ∀ w, w.IsComplex → 0 < x w}
      · rw [Set.indicator_of_mem hx]
        have : ⟨fun w : {w // IsReal w} ↦ x w.val, fun w : {w // IsComplex w} ↦ x w.val⟩
          ∈ Set.univ ×ˢ Set.univ.pi fun i ↦ Set.Ioi 0 := sorry
        rw [Set.indicator_of_mem this]
        have : realSpaceToMixedSpace K x ∈ s := sorry
        rw [← realSpaceToMixedSpace_apply, Set.indicator_of_mem this, mul_one]
        simp only [ENNReal.coe_finset_prod]
      · rw [Set.indicator_of_not_mem hx]
        rw [Set.mem_inter_iff] at hx
        rw [not_and'] at hx
        rw [Set.indicator_apply_eq_zero]
        intro h
        have := hx sorry
        dsimp only
        have : realSpaceToMixedSpace K x ∉ s := sorry
        rw [← realSpaceToMixedSpace_apply, Set.indicator_of_not_mem this, mul_zero]
    sorry
    sorry
    sorry
  sorry
  sorry
  sorry
  sorry

example :
    (realSpaceToMixedSpace K ∘ mixedSpaceToRealSpace K)⁻¹' (normLessThanOne K) =
      (normLessThanOne K) := by
  ext x
  simp only [Set.mem_preimage, Function.comp_apply, mixedSpaceToRealSpaceToMixedSpace_apply]
  have h_norm : ∀ w, normAtPlace w (fun w ↦ x.1 w, fun w ↦ ‖x.2 w‖) = normAtPlace w x := by
    intro w
    obtain hw | hw := isReal_or_isComplex w
    · simp_rw [normAtPlace_apply_isReal hw]
    · simp_rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.abs_ofReal,
        Complex.abs_abs]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine mem_normLessThanOne_of_normAtPlace_eq h ?_
    exact fun w ↦ (h_norm w).symm
  · exact mem_normLessThanOne_of_normAtPlace_eq h h_norm

theorem toto (s : Set (E K)) :
    (realSpaceToMixedSpace K ∘ mixedSpaceToRealSpace K)⁻¹' s = s ↔
      ∀ x, (x ∈ s ↔ ⟨fun w ↦ x.1 w, fun w ↦ ‖x.2 w‖⟩ ∈ s) := by
  refine ⟨?_, ?_⟩
  · intro hs x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · rwa [← hs, Set.mem_preimage, Function.comp_apply,
        mixedSpaceToRealSpaceToMixedSpace_apply] at hx
    · rwa [← mixedSpaceToRealSpaceToMixedSpace_apply, ← Set.mem_preimage, ← Set.mem_preimage,
        ← Set.preimage_comp, hs] at hx
  · intro hx
    ext
    rw [Set.mem_preimage, Function.comp_apply, mixedSpaceToRealSpaceToMixedSpace_apply, ← hx]

example (t : Set (InfinitePlace K → ℝ)) :
    (realSpaceToMixedSpace K ∘ mixedSpaceToRealSpace K)⁻¹' ((mixedSpaceToRealSpace K)⁻¹' t) =
      (mixedSpaceToRealSpace K)⁻¹' t := by
  rw [toto]
  intro x
  rw [Set.mem_preimage, Set.mem_preimage]
  simp only [mixedSpaceToRealSpace, Complex.norm_eq_abs, MonoidHom.coe_mk, OneHom.coe_mk,
    Complex.abs_ofReal, Complex.abs_abs]






open Real ENNReal in
theorem volume_closure_normLessOne :
    volume (closure (normLessThanOne K)) ≤
      2 ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := sorry

open Real ENNReal in
theorem volume_interior_normLessOne :
    2 ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal
      ≤ volume (interior (normLessThanOne K)) := sorry

example : volume (frontier (normLessThanOne K)) = 0 := by
  rw [frontier, measure_diff]
  · rw [tsub_eq_zero_iff_le]
    exact le_trans volume_closure_normLessOne volume_interior_normLessOne
  · exact interior_subset_closure
  · exact measurableSet_interior
  · rw [← lt_top_iff_ne_top]
    refine lt_of_le_of_lt (measure_mono interior_subset_closure) ?_
    refine lt_of_le_of_lt volume_closure_normLessOne ?_
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl -- ??

open Real ENNReal in
example : volume (normLessThanOne K) =
      2 ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := by
  refine le_antisymm ?_ ?_
  · refine le_trans ?_ volume_closure_normLessOne
    refine measure_mono ?_
    exact subset_closure
  · refine le_trans volume_interior_normLessOne ?_
    refine measure_mono ?_
    exact interior_subset





variable (K) in
def realSpaceToMixedSpace : (InfinitePlace K → ℝ) → (E K) :=
  fun x ↦ ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩

variable (K) in
def mixedSpaceToRealSpace : (E K) → (InfinitePlace K → ℝ) :=
  fun x ↦ fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩  else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖

theorem mixedSpaceToRealSpace_apply (x : E K) :
    mixedSpaceToRealSpace K x =
      fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩  else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖ := rfl

theorem volume_of_indicator_eq_indicator_norm (s : Set (E K)) (hs₀ : MeasurableSet s)
    (t : Set (InfinitePlace K → ℝ)) (ht₀ : MeasurableSet t)
    (h_ind : ∀ x, s.indicator (fun _ ↦ (1 : ENNReal)) x =
      t.indicator (fun _ ↦ 1) (mixedSpaceToRealSpace K x))
    (ht₁ : t ⊆ {x : InfinitePlace K → ℝ | ∀ w, w.IsReal → 0 < x w}) :
    volume s = (2 * NNReal.pi) ^ NrComplexPlaces K *
      ∫⁻ z in t, (∏ w : {w // IsComplex w}, ‖z w.val‖₊) := by
  let f : (InfinitePlace K → ℝ) →
      ({w : InfinitePlace K // w.IsReal} → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ) :=
    fun x ↦ ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩
  have hf : MeasurePreserving f := sorry
  calc
    _ = ∫⁻ x, ∫⁻ y, s.indicator (fun x ↦ 1) (x, y) := by
      rw [← setLIntegral_one, ← lintegral_indicator _ hs₀, Measure.volume_eq_prod, lintegral_prod]
      sorry
    _ = ∫⁻ x, (∫⋯∫⁻_Finset.univ, fun y ↦ t.indicator (fun x ↦ 1) (mixedSpaceToRealSpace K (x, y))
          ∂fun x ↦ volume) 0 ∂Measure.pi fun x ↦ volume := by
      simp_rw [h_ind, volume_pi, lintegral_eq_lmarginal_univ (0 : {w // IsComplex w} → ℂ)]
    _ = (∫⁻ x : {w // w.IsReal} → ℝ, (2 * NNReal.pi) ^ Finset.univ.card *
          ∫⁻ (y : { w // w.IsComplex } → ℝ), (∏ i, ‖y i‖₊) *
            t.indicator (fun x ↦ 1)
              fun w ↦ if hw : w.IsReal then x ⟨w, hw⟩ else y ⟨w, not_isReal_iff_isComplex.mp hw⟩
                ∂Measure.pi fun x ↦ volume ∂Measure.pi fun x ↦ volume) := by
      have := fun x : {w : InfinitePlace K // w.IsReal} → ℝ ↦ multiple_step
        (fun y : {w : InfinitePlace K // w.IsComplex} → ℝ  ↦ t.indicator (fun _ ↦ 1)
        (fun (w : InfinitePlace K) ↦ if h : w.IsReal then x ⟨w, sorry⟩ else y ⟨w, sorry⟩)) ?_ ?_ Finset.univ 0
      simp_rw [mixedSpaceToRealSpace_apply, this]
      simp_rw [ENNReal.coe_finset_prod, Pi.zero_apply, norm_zero, lmarginal_univ]
      rfl
      sorry
      sorry
    _ = (2 * NNReal.pi) ^ NrComplexPlaces K * ∫⁻ z in t, ∏ w : {w // w.IsComplex}, ‖z w.val‖₊ := by
      sorry

variable (K) in
def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def myMap : (InfinitePlace K → ℝ) →ₐ[ℝ] (E K) where
  toFun := fun x ↦ ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

theorem myMap_apply (c : InfinitePlace K → ℝ) : myMap c = ⟨fun w ↦ c w.val, fun w ↦ c w.val⟩ := rfl

theorem myMap_smul (x : InfinitePlace K → ℝ) (c : ℝ) :
    myMap (c • x) = c • (myMap x) := sorry

variable (K)

def logRepr (x : InfinitePlace K → ℝ) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex (equivFinRank K).symm).repr
        (logMap (myMap x))

theorem logRepr_apply (x : InfinitePlace K → ℝ) (i : {w : InfinitePlace K // w ≠ w₀}):
    logRepr K x i =
      (((basisUnitLattice K).ofZlatticeBasis ℝ (unitLattice K)).repr
        (logMap (myMap x))) (equivFinRank K i) := by
  simp [logRepr]

theorem logRepr_smul {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (myMap x) ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logRepr K (c • x) = logRepr K x := by
  simp_rw [logRepr, ← logMap_smul hx hc, LinearMapClass.map_smul]

def mapToUnitsPow₀ (c₀ : {w : InfinitePlace K // w ≠ w₀} → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ ∏ i, w (fundSystem K (equivFinRank K i)) ^ (c₀ i)

theorem mapToUnitsPow₀_apply (c₀ : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c₀ =  fun w ↦ ∏ i, w (fundSystem K (equivFinRank K i)) ^ (c₀ i) := rfl

--theorem continuous_mapToUnitsPow₀ :
--    Continuous (mapToUnitsPow₀ K) := by
--  refine continuous_pi fun w ↦ continuous_finset_prod _ fun i _ ↦ ?_
--  exact continuous_const.rpow (continuous_apply i) fun _ ↦ by left; simp

theorem norm_mapToUnitsPow₀ (c₀ : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (myMap (mapToUnitsPow₀ K c₀)) = 1 := by
  simp_rw [mapToUnitsPow₀_apply, ← Finset.prod_fn, map_prod, mixedEmbedding.norm_apply,
    myMap_apply]
  sorry

example {x y : InfinitePlace K → ℝ} (hx₀ : ∀ w, 0 < x w) (hy₀ : ∀ w, 0 < y w)
    (hx₁ : mixedEmbedding.norm (myMap x) = 1)
    (hy₁ : mixedEmbedding.norm (myMap x) = 1) {w' : InfinitePlace K}
    (h : ∀ w, w ≠ w' → x w = y w) : x = y := by sorry

theorem toto {x : InfinitePlace K → ℝ} (hx₀ : ∀ w, 0 < x w)
    (hx₁ : mixedEmbedding.norm (myMap x) = 1)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = x ↔ c = logRepr K x := sorry

theorem zap {x : InfinitePlace K → ℝ} :
    mapToUnitsPow₀ K (logRepr K x) = x := sorry

theorem zap' (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : logRepr K (mapToUnitsPow₀ K c) = c := sorry

def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ (c w₀) ^ (finrank ℚ K : ℝ)⁻¹ • mapToUnitsPow₀ K (fun w ↦ c w)
  invFun := fun x w ↦ if hw : w = w₀ then mixedEmbedding.norm (myMap x) else logRepr K x ⟨w, hw⟩
  source := Set.univ.pi fun w ↦ if w = w₀ then Set.Ioi 0 else Set.univ
  target := Set.univ.pi fun _ ↦ Set.Ioi 0
  map_source' := by
    intro x hx
    rw [Set.mem_univ_pi]
    intro w
    simp only [Pi.smul_apply, smul_eq_mul, Set.mem_Ioi]
    refine mul_pos ?_ ?_
    · sorry
    · sorry
  map_target' := by
    intro x hx
    rw [Set.mem_univ_pi]
    intro w
    rw [Set.mem_ite_univ_right, Set.mem_Ioi]
    intro hw
    dsimp only
    split_ifs
    sorry
  left_inv' := by
    intro c hc
    ext w
    refine dite_eq_iff'.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [myMap_smul, mixedEmbedding.norm_smul, h, norm_mapToUnitsPow₀, mul_one, abs_eq_self.mpr]
      sorry
      sorry
    · rw [logRepr_smul, zap']
      sorry
      sorry
  right_inv' := by
    intro x hx
    simp only [↓reduceDite, ne_eq, Subtype.coe_eta, dite_eq_ite]
    have : x = mixedEmbedding.norm (myMap x) ^ (finrank ℚ K : ℝ)⁻¹ •
      ((mixedEmbedding.norm (myMap x) ^ finrank ℚ K) • x) := sorry
    nth_rewrite 4 [this]
    sorry
    -- congr
    -- rw [toto]
    -- · rw [logRepr_smul]
    --   · ext w
    --     rw [if_neg w.prop]
    --   · sorry
    --   · sorry
    -- · simp only [Pi.smul_apply, smul_eq_mul]
    --   sorry
    -- · rw [myMap_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr]
    --   sorry
    --   sorry
  open_source := by
    dsimp only
    refine isOpen_set_pi Set.finite_univ fun _ _ ↦ ?_
    split_ifs
    exact isOpen_Ioi
    exact isOpen_univ
  open_target := by
    dsimp only
    refine isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioi
  continuousOn_toFun := by
    intro x hx
    dsimp only
    sorry
  continuousOn_invFun := sorry

def S : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

example : closure (S K) = Set.Icc 0 1 := by
  unfold S
  simp_rw [closure_pi_set, apply_ite, closure_Ioc zero_ne_one, closure_Ico zero_ne_one, ite_self,
    Set.pi_univ_Icc, Pi.zero_def, Pi.one_def]

example : interior (S K) = Set.univ.pi fun _ ↦ Set.Ioo 0 1 := by
  unfold S
  simp_rw [interior_pi_set Set.finite_univ, apply_ite, interior_Ioc, interior_Ico, ite_self]

theorem mapToUnitsPow_image :
  mapToUnitsPow K '' (S K) = myMap⁻¹' (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) := sorry

theorem main_eq :
  mixedSpaceToRealSpace K '' (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) =
    mapToUnitsPow K '' (S K) := sorry


example :
    closure (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w} ⊆
      mixedSpaceToRealSpace K ⁻¹' (mapToUnitsPow K '' (closure (S K))) := by
  rw [← Set.image_subset_iff]
  have := PartialHomeomorph.preimage_closure (mapToUnitsPow K).symm (S K)
  rw [PartialHomeomorph.symm_source] at this
  refine  (Set.image_inter_subset _ _ _).trans ?_



example :
    closure (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w} ⊆
      mixedSpaceToRealSpace K ⁻¹' (mapToUnitsPow K '' (closure (S K))) := by
  rw [← Set.image_subset_iff]
  refine  (Set.image_inter_subset _ _ _).trans ?_
  have := image_closure_subset_closure_image (by sorry : Continuous (mixedSpaceToRealSpace K))
    (s := normLessThanOne K)
  refine (Set.inter_subset_inter_left _ this).trans ?_

variable (K) in
def fusionEquiv₀ :
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // ¬IsReal w} → ℝ) ≃ᵐ
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  (MeasurableEquiv.refl _).prodCongr <|
    ⟨(Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex).piCongrLeft (fun _ ↦ ℝ),
      by measurability, by measurability⟩

theorem fusionEquiv₀_measure_preserving :
    MeasurePreserving (fusionEquiv₀ K) :=
  (MeasurePreserving.id volume).prod (volume_measurePreserving_piCongrLeft _ _)

def fusionEquiv :
    (InfinitePlace K → ℝ) ≃ᵐ
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)
       :=
  MeasurableEquiv.trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w))
      (fusionEquiv₀ K)


/-- The space `ℝ^r₁ × ℝ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "F" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)

-- Do you really a CLM? (probably just continuous) -- Also comp with fusionEquiv
def realSpaceToMixedSpace : (F K) →L[ℝ] (E K) where
  toFun := fun x ↦ ⟨fun w ↦ x.1 w, fun w ↦ x.2 w⟩
  map_add' _ _ := by
    simp_rw [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.ofReal_add, Prod.mk_add_mk]
    rfl
  map_smul' _ _ := by
    simp_rw [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
    rfl
  cont := continuous_fst.prod_mk <|
      continuous_pi
        fun _ ↦ Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_snd)

def mixedSpaceToRealSpace : (E K) → (F K) := fun x ↦ ⟨x.1, fun w ↦ ‖x.2 w‖⟩

example :
    normLessThanOne K =
      mixedSpaceToRealSpace⁻¹' (mixedSpaceToRealSpace '' (normLessThanOne K)) := by
  refine Set.Subset.antisymm_iff.mpr ⟨?_, ?_⟩
  · exact Set.subset_preimage_image _ _
  · intro a h
    rw [Set.mem_preimage] at h
    obtain ⟨x, hx₁, hx₂⟩ := h
    simp only [mixedSpaceToRealSpace, Prod.mk.injEq] at hx₂
    refine mem_normLessThanOne_of_normAtPlace_eq hx₁ ?_
    intro w
    obtain hw | hw := isReal_or_isComplex w
    · rw [normAtPlace_apply_isReal hw, normAtPlace_apply_isReal hw, hx₂.1]
    · rw [normAtPlace_apply_isComplex hw, normAtPlace_apply_isComplex hw]
      exact (congr_fun hx₂.2 ⟨w, hw⟩).symm

def A := closure (realSpaceToMixedSpace⁻¹' (normLessThanOne K))

theorem volume_of_indicator_eq_indicator_norm (s : Set (E K)) (hs₀ : MeasurableSet s)
    (t : Set (F K)) (ht₀ : MeasurableSet t)
    (h_ind : ∀ x y, s.indicator (fun _ ↦ (1 : ENNReal)) (x, y) =
      t.indicator (fun _ ↦ 1) (x, fun w ↦ ‖y w‖)) (ht₁ : t ⊆ {x : F K | ∀ w, 0 < x.2 w}) :
    volume s =
      (2 * NNReal.pi) ^ NrComplexPlaces K *
        ∫⁻ z in t, (∏ w : { w // IsComplex w}, ‖z.2 w‖₊) := by
  calc
    _ = ∫⁻ x, ∫⁻ y, s.indicator (fun x ↦ 1) (x, y) := by
      rw [← set_lintegral_one, Measure.volume_eq_prod, ← lintegral_indicator _ hs₀, lintegral_prod]
      sorry -- AEMeasurable (fun a ↦ s.indicator (fun x ↦ 1) a) (volume.prod volume)
    _ = (∫⁻ x, (∫⋯∫⁻_Finset.univ,
          fun y ↦ t.indicator (fun x ↦ 1) (x, fun w ↦ ‖y w‖)
            ∂fun _ ↦ volume) 0 ∂Measure.pi fun _ ↦ volume) := by
      simp_rw [h_ind, volume_pi, lintegral_eq_lmarginal_univ (0 : {w // IsComplex w} → ℂ)]
      rfl
    _ = ∫⁻ x, (2 * NNReal.pi) ^ NrComplexPlaces K *
        (∫⋯∫⁻_Finset.univ, fun y ↦
          (∏ i : { w // w.IsComplex }, ‖y i‖₊) *
            t.indicator (fun x ↦ 1) (x, fun w ↦ y w) ∂fun x ↦ volume) fun i ↦ 0 ∂volume := by
      congr! with _ x
      rw [multiple_step (fun y ↦ t.indicator (fun _ ↦ 1) (x, fun w ↦ y w)) ?_ ?_ Finset.univ 0]
      simp only [Finset.card_univ, ENNReal.coe_finset_prod, Pi.zero_apply, norm_zero,
        lmarginal_univ]
      sorry -- Measurable fun y ↦ t.indicator (fun x ↦ 1) (x, fun w ↦ y w)
      · intro x xᵢ i hxᵢ
        refine Set.indicator_of_not_mem ?_ _
        intro h
        have h' := ht₁ h
        simp at h'
        specialize h' i.val i.prop
        simp at h'
        linarith
    _ = (2 * NNReal.pi) ^ NrComplexPlaces K *
          ∫⁻ z in t, ∏ w : { w // w.IsComplex }, ‖z.2 w‖₊ := by
      rw [lintegral_const_mul]
      simp_rw [ENNReal.coe_finset_prod, lmarginal_univ]
      rw [lintegral_lintegral]
      rw [← lintegral_indicator]
      congr
      ext
      simp_rw [Set.indicator_apply, Prod.mk.eta, mul_ite, mul_one, mul_zero]
      exact ht₀
      sorry -- AEMeasurable (Function.uncurry fun a y ↦ (∏ a : { w // w.IsComplex }, ↑‖y a‖₊) * t.indicator (fun x ↦ 1) (a, fun w ↦ y w)) (volume.prod (Measure.pi fun x ↦ volume))
      sorry -- Measurable fun x ↦ (∫⋯∫⁻_Finset.univ, fun y ↦ ↑(∏ i : { w // w.IsComplex }, ‖y i‖₊) * t.indicator (fun x ↦ 1) (x, fun w ↦ y w) ∂fun x ↦ volume) fun i ↦ 0

theorem realSpaceToMixedSpace_apply_mem_normLessThanOne_iff {x : E K} :
    realSpaceToMixedSpace (x.1, fun w ↦ ‖x.2 w‖) ∈ normLessThanOne K ↔ x ∈ normLessThanOne K := by
  have : ∀ w, normAtPlace w (realSpaceToMixedSpace (x.1, fun w ↦ ‖x.2 w‖)) = normAtPlace w x := by
    intro w
    obtain hw | hw := isReal_or_isComplex w
    · simp_rw [normAtPlace_apply_isReal hw]
      rfl
    · simp_rw [normAtPlace_apply_isComplex hw]
      simp [realSpaceToMixedSpace]
  exact ⟨fun h ↦ mem_normLessThanOne_of_normAtPlace_eq h fun w ↦ (this w).symm,
    fun h ↦ mem_normLessThanOne_of_normAtPlace_eq h fun w ↦ this w⟩

example : volume (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) =
    (2 * NNReal.pi) ^ NrComplexPlaces K *
        ∫⁻ z in (realSpaceToMixedSpace⁻¹' (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w})),
          (∏ w : { w // IsComplex w}, ‖z.2 w‖₊) := by
  refine volume_of_indicator_eq_indicator_norm (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w})
    ?_ _ ?_ ?_ ?_
  · sorry
  · sorry
  · intro x y
    by_cases h : (x, y) ∈ normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
      refine ⟨?_, ?_⟩
      · convert realSpaceToMixedSpace_apply_mem_normLessThanOne_iff.mpr h.1
      · rw [Set.mem_setOf]
        intro w
        simpa [realSpaceToMixedSpace] using h.2 w
    · rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem]
      sorry
  · sorry

example (t : Set (F K)): volume (closure (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}) =
    (2 * NNReal.pi) ^ NrComplexPlaces K *
        ∫⁻ z in t, (∏ w : { w // IsComplex w}, ‖z.2 w‖₊) := by
  refine volume_of_indicator_eq_indicator_norm
    (closure (normLessThanOne K) ∩ {x | ∀ w, 0 < x.1 w}) ?_ _ ?_ ?_ ?_
  · sorry
  · sorry
  · intro x y
    sorry

--- Experiments

variable (K) in
def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

def myMap : (InfinitePlace K → ℝ) → (E K) := fun x ↦ ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩

theorem myMap_smul (x : InfinitePlace K → ℝ) (c : ℝ) :
    myMap (c • x) = c • (myMap x) := sorry

variable (K)

def logRepr (x : InfinitePlace K → ℝ) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex (equivFinRank K).symm).repr
        (logMap (myMap x))

theorem logRepr_apply (x : InfinitePlace K → ℝ) (i : {w : InfinitePlace K // w ≠ w₀}):
    logRepr K x i =
      (((basisUnitLattice K).ofZlatticeBasis ℝ (unitLattice K)).repr
        (logMap (myMap x))) (equivFinRank K i) := by
  simp [logRepr]

theorem logRepr_smul {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (myMap x) ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logRepr K (c • x) = logRepr K x := by
  simp_rw [logRepr, ← logMap_smul hx hc, myMap, Prod.smul_mk, Pi.smul_def, smul_eq_mul,
    Complex.ofReal_mul, Complex.real_smul]

def mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ ∏ i, w (fundSystem K (equivFinRank K i)) ^ (c i)

theorem continuous_mapToUnitsPow₀ :
    Continuous (mapToUnitsPow₀ K) := by
  refine continuous_pi fun w ↦ continuous_finset_prod _ fun i _ ↦ ?_
  exact continuous_const.rpow (continuous_apply i) fun _ ↦ by left; simp

example {x y : InfinitePlace K → ℝ} (hx₀ : ∀ w, 0 < x w) (hy₀ : ∀ w, 0 < y w)
    (hx₁ : mixedEmbedding.norm (myMap x) = 1)
    (hy₁ : mixedEmbedding.norm (myMap x) = 1) {w' : InfinitePlace K}
    (h : ∀ w, w ≠ w' → x w = y w) : x = y := by sorry

theorem toto₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (myMap (mapToUnitsPow₀ K c)) = 1 := sorry

theorem toto {x : InfinitePlace K → ℝ} (hx₀ : ∀ w, 0 < x w)
    (hx₁ : mixedEmbedding.norm (myMap x) = 1)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = x ↔ c = logRepr K x := sorry

theorem zap {x : InfinitePlace K → ℝ} :
    mapToUnitsPow₀ K (logRepr K x) = x := sorry

theorem zap' (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : logRepr K (mapToUnitsPow₀ K c) = c := sorry

def mapToUnitsPow : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun c ↦ (c w₀) ^ (finrank ℚ K : ℝ)⁻¹ • mapToUnitsPow₀ K (fun w ↦ c w)
  invFun := fun x w ↦ if hw : w = w₀ then mixedEmbedding.norm (myMap x) else logRepr K x ⟨w, hw⟩
  source := sorry
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := by
    intro c hc
    ext w
    refine dite_eq_iff'.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [myMap_smul, mixedEmbedding.norm_smul, h, toto₀, mul_one, abs_eq_self.mpr]
      sorry
      sorry
    · rw [logRepr_smul, zap']
      sorry
      sorry
  right_inv' := by
    intro x hx
    simp only [↓reduceDite, ne_eq, Subtype.coe_eta, dite_eq_ite]
    have : x = mixedEmbedding.norm (myMap x) ^ (finrank ℚ K : ℝ)⁻¹ •
      ((mixedEmbedding.norm (myMap x) ^ finrank ℚ K) • x) := sorry
    nth_rewrite 4 [this]
    congr
    rw [toto]
    · rw [logRepr_smul]
      · ext w
        rw [if_neg w.prop]
      · sorry
      · sorry
    · sorry
    · rw [myMap_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr]
      sorry
      sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := by
    intro x hx
    dsimp only
    sorry
  continuousOn_invFun := sorry





-- theorem volume_normLessOne₀ :
--     volume (normLessThanOne₀ K) =
--       (2 * NNReal.pi) ^ NrComplexPlaces K *
--         ∫⁻ z in (normLessThanOne₁ K), (∏ w : { w // IsComplex w}, ‖z.2 w‖₊) := by
--   sorry

theorem measurableSet_normLessThanOne₀ :
    MeasurableSet (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) := by
  refine MeasurableSet.inter ?_ ?_
  exact measurableSet_normLessThanOne K
  convert measurableSet_positiveAt (K := K) Finset.univ
  simp only [Subtype.forall, Finset.mem_univ, true_implies]

variable (K) in
abbrev normLessThanOne₀ := normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}

variable (K) in
def normLessThanOne₁ :
    Set (({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
    {x | (∀ w, 0 < x.1 w) ∧ (∀ w, 0 < x.2 w) ∧
      (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w,
        fun w : {w : InfinitePlace K // IsComplex w} ↦ (x.2 w : ℂ)) ∈ normLessThanOne K}

theorem measurableSet_normLessThanOne₁ :
    MeasurableSet (normLessThanOne₁ K) := by
  let f : ({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℝ) → (E K) :=
    fun (x, y) ↦ (x, fun w ↦ y w)
  have hf : Measurable f := by
    refine Measurable.prod_mk ?_ ?_
    · exact measurable_fst
    · refine measurable_pi_iff.mpr fun _ ↦ ?_
      have : Measurable (Complex.ofReal) := by
        refine Continuous.measurable ?_
        exact Complex.continuous_ofReal
      refine Measurable.comp this ?_
      exact Measurable.comp (measurable_pi_apply _) measurable_snd
  let A := f ⁻¹' (normLessThanOne K)
  have mesA : MeasurableSet A := hf (measurableSet_normLessThanOne K)
  have : normLessThanOne₁ K = {x | (∀ w, 0 < x.1 w)}  ∩ {x | (∀ w, 0 < x.2 w)} ∩ A := by
    ext
    simp [normLessThanOne₁]
    aesop
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) mesA
  · refine MeasurableSet.congr (s := ⋂ z, {x | 0 < x.1 z}) ?_ ?_
    · refine  MeasurableSet.iInter fun _ ↦ ?_
      · exact measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const <|
        (measurable_pi_apply _).comp measurable_fst
    · ext
      simp_rw [Set.mem_iInter, Subtype.forall, Set.mem_setOf_eq]
  · refine MeasurableSet.congr (s := ⋂ z, {x | 0 < x.2 z}) ?_ ?_
    · refine  MeasurableSet.iInter fun _ ↦ ?_
      · exact measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const <|
        (measurable_pi_apply _).comp measurable_snd
    · ext
      simp_rw [Set.mem_iInter, Subtype.forall, Set.mem_setOf_eq]

theorem indicator_eq_indicator (x : {w : InfinitePlace K // IsReal w} → ℝ)
    (y : {w : InfinitePlace K // IsComplex w} → ℂ) :
    (normLessThanOne₀ K).indicator (fun _ ↦ (1 : ENNReal)) (x, y) =
      (normLessThanOne₁ K).indicator (fun _ ↦ (1 : ENNReal)) (x, fun w ↦ (fun i ↦ ‖y i‖) w) := by
  have : ∀ ⦃x y⦄, (x, y) ∈ normLessThanOne₀ K ↔ (x, (fun w ↦ ‖y w‖)) ∈ (normLessThanOne₁ K) := by
    intro x y
    refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
    · sorry -- exact fun w ↦ h.2 w.val w.prop
    · intro w
      have := mixedEmbedding.norm_ne_zero_iff.mp (norm_pos_of_mem h.1.1).ne.symm w.val
      rw [normAtPlace_apply_isComplex w.prop, norm_ne_zero_iff] at this
      simp [this]
    · exact mem_normLessThanOne_of_normAtPlace_eq h.1 fun w ↦ by simp [normAtPlace]
    · exact mem_normLessThanOne_of_normAtPlace_eq h.2.2 fun w ↦ by simp [normAtPlace]
    · sorry -- exact fun w hw ↦ h.1 ⟨w, hw⟩
  by_cases h : (x, y) ∈ normLessThanOne₀ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem (this.not.mp h)]

theorem volume_normLessOne₀ :
    volume (normLessThanOne₀ K) =
      (2 * NNReal.pi) ^ NrComplexPlaces K *
        ∫⁻ z in (normLessThanOne₁ K), (∏ w : { w // IsComplex w}, ‖z.2 w‖₊) := by
  have h₀ : Measurable ((normLessThanOne₀ K).indicator (fun _ ↦ (1 : ENNReal))) :=
    (measurable_indicator_const_iff 1).mpr <| sorry -- measurableSet_normLessThanOne₀ K
  rw [← set_lintegral_one, Measure.volume_eq_prod, ← lintegral_indicator _ (measurableSet_normLessThanOne₀ K),
    lintegral_prod _ h₀.aemeasurable]
  simp_rw [indicator_eq_indicator, volume_pi,
    lintegral_eq_lmarginal_univ (0 : {w // IsComplex w} → ℂ)]
  have := fun x ↦ multiple_step (fun y ↦ (normLessThanOne₁ K).indicator (fun _ ↦ 1)
      (x, fun w ↦ y w)) ?_ ?_ Finset.univ 0
  dsimp only at this
  conv_lhs =>
    enter [2, x]
    rw [this x]
  simp only [Finset.card_univ, ENNReal.coe_finset_prod, Pi.zero_apply, norm_zero, lmarginal_univ]
  rw [lintegral_const_mul, NrComplexPlaces]
  rw [lintegral_lintegral]
  rw [← lintegral_indicator]
  · congr
    ext z
    rw [← ENNReal.coe_finset_prod]
    simp_rw [Set.indicator_apply]
    simp only [ENNReal.coe_finset_prod, Prod.mk.eta, mul_ite, mul_one, mul_zero]
  · exact measurableSet_normLessThanOne₁ K
  · refine Measurable.aemeasurable ?_
    rw [Function.uncurry_def]
    refine Measurable.mul ?_ ?_
    · refine Finset.measurable_prod _ fun _ _ ↦ ?_
      simp only [measurable_coe_nnreal_ennreal_iff]
      refine measurable_nnnorm.comp ?_
      exact Measurable.eval measurable_snd
    · refine Measurable.indicator ?_ ?_
      exact measurable_const
      exact measurableSet_normLessThanOne₁ K
  · refine Measurable.lintegral_prod_right ?_
    rw [Function.uncurry_def]
    -- Duplicate of the above code
    refine Measurable.mul ?_ ?_
    · refine Finset.measurable_prod _ fun _ _ ↦ ?_
      simp only [measurable_coe_nnreal_ennreal_iff]
      refine measurable_nnnorm.comp ?_
      exact Measurable.eval measurable_snd
    · refine Measurable.indicator ?_ ?_
      exact measurable_const
      exact measurableSet_normLessThanOne₁ K
  · refine Measurable.indicator ?_ ?_
    · exact measurable_const
    · let f : ({w : InfinitePlace K // IsComplex w} → ℝ) →
        ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ) := fun y ↦ (x, fun w ↦ y w)
      let s := f ⁻¹' (normLessThanOne₁ K)
      refine MeasurableSet.congr (s := s) ?_ ?_
      · dsimp only [s]
        refine MeasurableSet.preimage (measurableSet_normLessThanOne₁ K) ?_
        dsimp only [f]
        rw [measurable_prod]
        refine ⟨?_, ?_⟩
        · simp
        · exact fun ⦃t⦄ a ↦ a -- ??
      · ext
        simp [s, normLessThanOne₁, Set.mem_def]
        rfl
  · intro x _ w h
    rw [Set.indicator_apply_eq_zero]
    simp only [one_ne_zero, imp_false]
    intro hx
    have := hx.2.1 w
    simp at this
    linarith

variable (K)

def fusionEquiv₀ :
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // ¬IsReal w} → ℝ) ≃ᵐ
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  (MeasurableEquiv.refl _).prodCongr <|
    ⟨(Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex).piCongrLeft (fun _ ↦ ℝ),
      by measurability, by measurability⟩

theorem fusionEquiv₀_measure_preserving :
    MeasurePreserving (fusionEquiv₀ K) :=
  (MeasurePreserving.id volume).prod (volume_measurePreserving_piCongrLeft _ _)

def fusionEquiv :
    (InfinitePlace K → ℝ) ≃ᵐ
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)
       :=
  MeasurableEquiv.trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w))
      (fusionEquiv₀ K)

theorem fusionEquiv_measure_preserving :
    MeasurePreserving (fusionEquiv K) := by
  unfold fusionEquiv
  refine MeasurePreserving.trans ?_ (fusionEquiv₀_measure_preserving K)
  exact volume_preserving_piEquivPiSubtypeProd _ _

theorem fusionEquiv_apply (x : InfinitePlace K → ℝ) :
    fusionEquiv K x = (fun w ↦ x w.val, fun w ↦ x w.val) := rfl

theorem fusionEquiv_symm_apply
    (x : ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    (fusionEquiv K).symm x = fun w ↦
      if hw : IsReal w then x.1 ⟨w, hw⟩ else x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩ := rfl

def normLessThanOne₂ : Set (InfinitePlace K → ℝ) := (fusionEquiv K)⁻¹' (normLessThanOne₁ K)

def equivFinRank : {w : InfinitePlace K // w ≠ w₀} ≃ Fin (rank K) := by
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

-- That's a terrible name
def normUnits : {w : InfinitePlace K // w ≠ w₀} → ((InfinitePlace K) → ℝ) :=
  fun i w ↦ w (fundSystem K (equivFinRank K i))

theorem normUnits_eq (i : {w : InfinitePlace K // w ≠ w₀}) (w : InfinitePlace K) :
    normUnits K i w = w (fundSystem K (equivFinRank K i)) := rfl

theorem normUnits_pos (i : {w : InfinitePlace K // w ≠ w₀}) (w : InfinitePlace K) :
    0 < normUnits K i w := by
  simp_rw [normUnits_eq, pos_iff, ne_eq, RingOfIntegers.coe_eq_zero_iff, Units.ne_zero,
    not_false_eq_true]

def normUnitsEvalProd (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : InfinitePlace K → ℝ :=
  fun w ↦ ∏ i, (normUnits K i w) ^ (c i)

theorem normUnitsEvalProd_def (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    normUnitsEvalProd K c w = ∏ i, (normUnits K i w) ^ (c i) := rfl

theorem normUnitsEvalProd_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < normUnitsEvalProd K c w :=
  Finset.prod_pos fun _ _ ↦ Real.rpow_pos_of_pos (normUnits_pos K _ _) _

theorem prod_normUnitsEvalProd_pow_mult (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    ∏ w : InfinitePlace K, normUnitsEvalProd K c w ^ w.mult = 1 := by
  simp_rw [normUnitsEvalProd_def, ← Finset.prod_pow, ← Real.rpow_mul_natCast
    (normUnits_pos _ _ _).le, fun i ↦ mul_comm (c i), Real.rpow_natCast_mul
    (normUnits_pos _ _ _).le]
  rw [Finset.prod_comm]
  have : ∀ i w, 0 ≤ normUnits K i w ^ w.mult := by
        intro _ _
        refine pow_nonneg ?_ _
        exact (normUnits_pos _ _ _).le
  simp_rw [Real.finset_prod_rpow _ _ (fun _ _ ↦ this _ _), normUnits, prod_eq_abs_norm, Units.norm,
    Rat.cast_one, Real.one_rpow, Finset.prod_const_one]

theorem prod_normUnitsEvalProd (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    ∏ w : InfinitePlace K, normUnitsEvalProd K c w =
      (∏ w : {w : InfinitePlace K // IsComplex w}, normUnitsEvalProd K c w)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv₀, ← Fintype.prod_subtype_mul_prod_subtype (fun w ↦ IsReal w)]
  rw [← (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)).prod_comp]
  simp_rw [Equiv.subtypeEquivRight_apply_coe]
  · rw [mul_assoc, ← sq, ← Finset.prod_pow]
    convert_to ∏ w, ((normUnitsEvalProd K c w) ^ w.mult) = 1
    · rw [← Fintype.prod_subtype_mul_prod_subtype (fun w ↦ IsReal w)]
      congr
      · ext w
        rw [mult, if_pos w.prop, pow_one]
      · ext w
        rw [mult, if_neg w.prop]
    · exact prod_normUnitsEvalProd_pow_mult K c
  · rw [Finset.prod_ne_zero_iff]
    intro _ _
    rw [normUnitsEvalProd_def]
    rw [Finset.prod_ne_zero_iff]
    intro _ _
    refine Real.rpow_ne_zero_of_pos ?_ _
    exact normUnits_pos K _ _

theorem normAtPlace_eq (x : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    normAtPlace w ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩ = |x w| := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_isReal hw, Real.norm_eq_abs]
  · rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.abs_ofReal]

theorem normReal_eq (x : InfinitePlace K → ℝ) (hx : ∀ w, 0 ≤ x w) :
    mixedEmbedding.norm ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩ = ∏ w, (x w) ^ mult w :=
  Finset.prod_congr rfl fun w _ ↦ by rw [normAtPlace_eq, abs_eq_self.mpr (hx _)]

theorem normReal_normUnitsEvalProd (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm ⟨fun w ↦ normUnitsEvalProd K c w.val,
      fun w ↦ normUnitsEvalProd K c w.val⟩ = 1 := by
  rw [normReal_eq]
  exact prod_normUnitsEvalProd_pow_mult K c
  intro _
  exact (normUnitsEvalProd_pos _ _ _).le

def logRepr (x : InfinitePlace K → ℝ) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  (((basisUnitLattice K).ofZlatticeBasis ℝ).reindex (equivFinRank K).symm).equivFun
        (logMap ⟨fun w ↦ x w.val, fun w ↦ x w.val⟩)

theorem logRepr_apply (x : InfinitePlace K → ℝ) (i : {w : InfinitePlace K // w ≠ w₀}):
    logRepr K x i =
      (((basisUnitLattice K).ofZlatticeBasis ℝ (unitLattice K) ).repr
        (logMap (fun w ↦ x w, fun w ↦ x w))) (equivFinRank K i) := by
  simp [logRepr]

theorem normUnitsEvalProd_eq_iff {x : InfinitePlace K → ℝ} {c : {w : InfinitePlace K // w ≠ w₀} → ℝ}
    (hx₀ : mixedEmbedding.norm (⟨fun w ↦ x w.val, fun w ↦ x w.val⟩) = 1)
    (hx₁ : ∀ w, 0 < x w) :
    normUnitsEvalProd K c = x ↔ c = logRepr K x := by
  have h₀ : ∀ w,  0 < ∏ i : { w // w ≠ w₀ }, normUnits K i w ^ c i := by
    intro _
    refine Finset.prod_pos fun _ _ ↦ ?_
    refine Real.rpow_pos_of_pos ?_ _
    exact normUnits_pos K _ _
  suffices (∀ w : {w // w ≠ w₀}, normUnitsEvalProd K c w = x w.val) ↔ c = logRepr K x by
    rw [← this, Function.funext_iff]
    refine ⟨fun h w ↦ h w, fun h w ↦ ?_⟩
    by_cases hw : w = w₀
    · simp_rw [normUnitsEvalProd_def, hw] at h ⊢
      have : ∏ w, ∏ i, (normUnits K i w ^ c i) ^ w.mult = ∏ w, x w ^ w.mult := by
        rw [← normReal_eq, hx₀]
        simp_rw [Finset.prod_pow]
        simp_rw [← normUnitsEvalProd_def]
        rw [prod_normUnitsEvalProd_pow_mult]
        exact fun _ ↦ (hx₁ _).le
      rw [← Finset.univ.prod_erase_mul _ (Finset.mem_univ w₀),
        ← Finset.univ.prod_erase_mul _ (Finset.mem_univ w₀)] at this
      rw [show (∏ w ∈ Finset.univ.erase w₀, ∏ i : { w // w ≠ w₀ }, (normUnits K i w ^ c i) ^ w.mult)
        = (∏ w ∈ Finset.univ.erase (w₀ : InfinitePlace K), (x w) ^ w.mult) by
          refine Finset.prod_congr rfl fun z hz ↦ ?_
          have := h ⟨z, (Finset.mem_erase.mp hz).1⟩
          rw [← this, Finset.prod_pow]] at this
      rwa [mul_cancel_left_mem_nonZeroDivisors, Finset.prod_pow, pow_left_inj] at this
      exact (h₀ _).le
      exact (hx₁ w₀).le
      exact mult_ne_zero
      · rw [mem_nonZeroDivisors_iff_ne_zero, Finset.prod_ne_zero_iff]
        intro _ _
        refine pow_ne_zero _ ?_
        exact ne_of_gt (hx₁ _)
    · exact h ⟨w, hw⟩
  have hl₁ : ∀ w : InfinitePlace K, (w.mult : ℝ) ∈ ℝ⁰ := by
    intro _
    rw [mem_nonZeroDivisors_iff_ne_zero, Nat.cast_ne_zero]
    exact mult_ne_zero
  have hl₂ : ∀ i (w : InfinitePlace K), 0 < w (fundSystem K (equivFinRank K i)) := by
    intro _ _
    exact normUnits_pos K _ _
  have hl₃ : ∀ i (w : InfinitePlace K), w (fundSystem K (equivFinRank K i)) ^ c i ≠ 0 := by
    intro _ _
    exact Real.rpow_ne_zero_of_pos (hl₂ _ _) _
  simp_rw [logRepr, ← Basis.sum_eq_iff_eq_equivFun, Basis.coe_reindex, Equiv.symm_symm,
    Function.comp_apply, Basis.ofZlatticeBasis_apply, ← logEmbedding_fundSystem,
    Function.funext_iff, logMap_apply_of_norm_one hx₀, Finset.sum_apply, Pi.smul_apply,
    logEmbedding_component, smul_eq_mul, ← mul_assoc, fun i ↦ mul_comm (c i), mul_assoc,
    ← Finset.mul_sum, mul_cancel_left_mem_nonZeroDivisors (hl₁ _), ← Real.log_rpow (hl₂ _ _),
    ← Real.log_prod _ _ (fun _ _ ↦ (hl₃ _ _)), normAtPlace_eq, abs_eq_self.mpr (hx₁ _).le,
    ← normUnits_eq, normUnitsEvalProd_def]
  refine ⟨fun h w ↦ congr_arg Real.log (h w), fun h w ↦ ?_⟩
  refine Real.log_injOn_pos ?_ ?_ (h w)
  · exact h₀ _
  · exact hx₁ _

theorem logRepr_normUnitsEvalProd_eq {c : {w : InfinitePlace K // w ≠ w₀} → ℝ} :
    logRepr K (normUnitsEvalProd K c) = c := by
  rw [eq_comm, ← normUnitsEvalProd_eq_iff]
  exact normReal_normUnitsEvalProd K c
  exact fun w ↦ normUnitsEvalProd_pos K c w

theorem normEqOne₂_eq_image : {x | x ∈ normLessThanOne₂ K ∧
    mixedEmbedding.norm (⟨fun w ↦ x w.val, fun w ↦ x w.val⟩) = 1} =
    (normUnitsEvalProd K) '' (Set.univ.pi fun _ ↦ Set.Ico 0 1) := by
  ext x
  simp_rw [Set.mem_setOf_eq, normLessThanOne₂, Set.mem_image, Set.mem_preimage, fusionEquiv_apply,
    normLessThanOne₁, Set.mem_setOf_eq, fundamentalCone, Set.mem_diff, Set.mem_preimage,
    Set.mem_setOf_eq, ← ne_eq, Zspan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies,
    Equiv.forall_congr_left (equivFinRank K).symm, Equiv.symm_symm, ← logRepr_apply]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hx₁, hx₂, ⟨hx₃, _⟩, _⟩, hx₄⟩
    refine ⟨logRepr K x, hx₃, (normUnitsEvalProd_eq_iff K hx₄ fun w ↦ ?_).mpr rfl⟩
    obtain hw | hw :=  isReal_or_isComplex w
    · exact hx₁ ⟨w, hw⟩
    · exact hx₂ ⟨w, hw⟩
  · rintro ⟨c, hc₁, rfl⟩
    refine ⟨⟨fun w ↦ normUnitsEvalProd_pos K c w, fun w ↦ normUnitsEvalProd_pos K c w,
      ⟨?_, by simp [normReal_normUnitsEvalProd]⟩, by simp [normReal_normUnitsEvalProd]⟩, by
      simp [normReal_normUnitsEvalProd]⟩
    convert hc₁
    rw [eq_comm, ← normUnitsEvalProd_eq_iff]
    · simp [normReal_normUnitsEvalProd]
    · exact fun w ↦ normUnitsEvalProd_pos K c w

def normUnitsEval (c : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  (c w₀) • normUnitsEvalProd K (fun w ↦ c w)

def S : Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

theorem measurable_S :
    MeasurableSet (S K) := by
  refine MeasurableSet.univ_pi fun w ↦ ?_
  refine MeasurableSet.ite' ?_ ?_
  exact fun _ ↦ measurableSet_Ioc
  exact fun _ ↦ measurableSet_Ico

theorem normUnitsEval_injOn :
    Set.InjOn (normUnitsEval K) (S K) := by
  intro c hc c' hc' h
  have h₀ : 0 < c w₀ := by
    rw [S, Set.mem_univ_pi] at hc
    specialize hc w₀
    rw [if_pos rfl] at hc
    exact hc.1
  have h₀' : 0 < c' w₀ := by
    rw [S, Set.mem_univ_pi] at hc'
    specialize hc' w₀
    rw [if_pos rfl] at hc'
    exact hc'.1
  suffices c w₀ = c' w₀ by
    rw [normUnitsEval, normUnitsEval, this] at h
    rw [IsUnit.smul_left_cancel] at h
    rw [normUnitsEvalProd_eq_iff] at h
    rw [logRepr_normUnitsEvalProd_eq] at h
    ext w
    by_cases hw : w = w₀
    · rw [hw, this]
    · rw [Function.funext_iff] at h
      exact h ⟨w, hw⟩
    exact normReal_normUnitsEvalProd K fun w ↦ c' w
    intro _
    exact normUnitsEvalProd_pos K _ _
    rw [isUnit_iff_ne_zero]
    exact ne_of_gt h₀'
  have := congr_arg (fun x ↦ mixedEmbedding.norm (⟨fun w ↦ x w.val, fun w ↦ x w.val⟩)) h
  simp_rw [normUnitsEval, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, ← Complex.real_smul,
    ← smul_eq_mul, ← Pi.smul_def, ← Prod.smul_mk, mixedEmbedding.norm_smul,
    normReal_normUnitsEvalProd, mul_one] at this
  rwa [pow_left_inj, abs_eq_self.mpr, abs_eq_self.mpr] at this
  any_goals positivity
  refine ne_of_gt ?_
  exact finrank_pos

theorem smul_mem_normLessThanOne₂ {x : InfinitePlace K → ℝ} (hx : x ∈ normLessThanOne₂ K) {c : ℝ}
    (hc : c ∈ Set.Ioc 0 1) :
    c • x ∈ normLessThanOne₂ K := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    simp only [fusionEquiv_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_pos hc.1 (hx.1 w)
  · intro w
    simp only [fusionEquiv_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_pos hc.1 (hx.2.1 w)
  · have := hx.2.2
    simp_rw [fusionEquiv_apply, Pi.smul_apply]
    have : ((fun w ↦ c • x w.val, fun w ↦ (c • x w.val : ℝ)) : E K) =
        c • ((fun w ↦ x w.val, fun w ↦ x w.val) : E K) := by
      simp_rw [Prod.smul_mk, Pi.smul_def, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
    rw [this]
    refine smul_normLessThanOne_subset K (c := c) ?_ ?_ ?_
    · exact ne_of_gt hc.1
    · rw [abs_eq_self.mpr hc.1.le]
      exact hc.2
    · rwa [Set.smul_mem_smul_set_iff₀ (ne_of_gt hc.1)]

theorem normLessThanOne₂_eq_image : normLessThanOne₂ K = (normUnitsEval K) '' (S K) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨hx₁, hx₂, hx₃⟩
    obtain ⟨d, hd₀, hd₁, hx₄⟩ := exists_mem_smul_normEqOne hx₃
    have : d⁻¹ • x ∈ {x | x ∈ normLessThanOne₂ K ∧
        mixedEmbedding.norm (⟨fun w ↦ x w.val, fun w ↦ x w.val⟩) = 1} := by
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hd₀), Set.mem_setOf_eq] at hx₄
      simp_rw [fusionEquiv_apply, Prod.smul_mk, Pi.smul_def, smul_eq_mul, Complex.real_smul] at hx₄
      refine ⟨⟨?_, ?_, ⟨?_, ?_⟩⟩, ?_⟩
      · exact fun w ↦ mul_pos (inv_pos.mpr hd₀) (hx₁ w)
      · exact fun w ↦ mul_pos (inv_pos.mpr hd₀) (hx₂ w)
      · simp only [fusionEquiv_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
        exact hx₄.1
      · simp only [fusionEquiv_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
        rw [hx₄.2]
      · simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
        exact hx₄.2
    rw [normEqOne₂_eq_image] at this
    obtain ⟨c, hc₀, hc₁⟩ := this
    refine ⟨?_, ?_, ?_⟩
    · exact fun w ↦ if hw : w = w₀ then d else c ⟨w, hw⟩
    · rw [S, Set.mem_univ_pi]
      intro w
      by_cases hw : w = w₀
      · rw [dif_pos hw, if_pos hw]
        exact ⟨hd₀, hd₁⟩
      · rw [dif_neg hw, if_neg hw]
        exact hc₀ ⟨w, hw⟩ (Set.mem_univ _)
    · rw [normUnitsEval]
      simp only [↓reduceDite, ne_eq, Subtype.coe_eta, dite_eq_ite]
      conv_lhs =>
        enter [2, _w, 2, w]
        rw [if_neg w.prop]
      rw [hc₁, smul_inv_smul₀]
      exact ne_of_gt hd₀
  · rintro ⟨c, hc, rfl⟩
    rw [normUnitsEval]
    refine smul_mem_normLessThanOne₂ K ?_ ?_
    · have : normUnitsEvalProd K (fun w ↦ c w) ∈
          (normUnitsEvalProd K) '' (Set.univ.pi fun _ ↦ Set.Ico 0 1) := by
        refine ⟨fun w ↦ c w, ?_, rfl⟩
        rw [Set.mem_univ_pi]
        intro w
        specialize hc w (Set.mem_univ _)
        simp_rw [if_neg w.prop] at hc
        exact hc
      rw [← normEqOne₂_eq_image] at this
      exact this.1
    · rw [S, Set.mem_univ_pi] at hc
      specialize hc w₀
      rwa [if_pos rfl] at hc

def normUnitsEvalSingle (i : InfinitePlace K) (c : InfinitePlace K → ℝ) : InfinitePlace K → ℝ :=
  if hi : i = w₀ then fun _ ↦ c w₀ else normUnits K ⟨i, hi⟩ ^ c i

theorem prod_normUnitsEvalSingle_apply (c : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    ∏ i, normUnitsEvalSingle K i c w = normUnitsEval K c w := by
  simp_rw [normUnitsEvalSingle, normUnitsEval]
  unfold normUnitsEvalProd
  rw [← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀), dif_pos rfl]
  rw [Finset.prod_subtype (Finset.univ.erase w₀) (p := fun w ↦ w ≠ w₀), Pi.smul_apply, smul_eq_mul]
  congr 2 with i
  rw [dif_neg i.prop, Pi.pow_apply]
  intro _
  simp_rw [Finset.mem_erase, Finset.mem_univ, and_true]

def FDeriv_normUnitsEvalSingle (i w : InfinitePlace K) (c : InfinitePlace K → ℝ) :
    (InfinitePlace K → ℝ) →L[ℝ] ℝ := by
  exact if hi : i = w₀ then ContinuousLinearMap.proj w₀ else
    (normUnits K ⟨i, hi⟩ w ^ (c i) * (normUnits K ⟨i, hi⟩ w).log) • ContinuousLinearMap.proj i

theorem hasFDeriv_normUnitsEvalSingle (i w : InfinitePlace K) (x : InfinitePlace K → ℝ) :
    HasFDerivAt (fun x ↦ normUnitsEvalSingle K i x w) (FDeriv_normUnitsEvalSingle K i w x) x := by
  unfold normUnitsEvalSingle
  unfold FDeriv_normUnitsEvalSingle
  split_ifs
  · exact hasFDerivAt_apply w₀ x
  · exact HasFDerivAt.const_rpow (hasFDerivAt_apply i x) (normUnits_pos K _ w)

def jacobianCoeff (w i : InfinitePlace K) : (InfinitePlace K → ℝ) → ℝ :=
    fun c ↦ if hi : i = w₀ then 1 else (c w₀) * (normUnits K ⟨i, hi⟩ w).log

def jacobian : (InfinitePlace K → ℝ) → (InfinitePlace K → ℝ) →L[ℝ] InfinitePlace K → ℝ := by
  intro c
  refine ContinuousLinearMap.pi ?_
  intro i
  exact (normUnitsEvalProd K (fun w ↦ c w) i •
    ∑ w, (jacobianCoeff K i w c) • ContinuousLinearMap.proj w)

theorem jacobian_det (c : InfinitePlace K → ℝ) :
    |(jacobian K c).det| =
      (∏ w : {w : InfinitePlace K // w.IsComplex }, normUnitsEvalProd K (fun w ↦ c w) w)⁻¹ *
        2⁻¹ ^ NrComplexPlaces K * |c w₀| ^ (rank K) * (finrank ℚ K) * regulator K := by
  have : LinearMap.toMatrix' (jacobian K c).toLinearMap =
      Matrix.of fun w i ↦ normUnitsEvalProd K (fun w ↦ c w) w * jacobianCoeff K w i c := by
    ext;
    simp_rw [jacobian, ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_smul,
      ContinuousLinearMap.coe_sum, LinearMap.toMatrix'_apply, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', this]
  rw [Matrix.det_mul_column, prod_normUnitsEvalProd, ← Matrix.det_transpose]
  simp_rw [jacobianCoeff]
  simp_rw [normUnits]
  rw [mul_assoc, finrank_mul_regulator_eq_det K w₀ (equivFinRank K)]
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
    exact Finset.prod_nonneg fun _ _ ↦ (normUnitsEvalProd_pos K _ _).le
  · ext
    simp only [Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul, mul_ite]
    split_ifs
    · rw [inv_mul_cancel]
      rw [Nat.cast_ne_zero]
      exact mult_ne_zero
    · ring_nf
      simp

theorem hasFDeriv_normUnitsEval (c : InfinitePlace K → ℝ) :
    HasFDerivAt (normUnitsEval K) (jacobian K c) c := by
  rw [hasFDerivAt_pi']
  intro w
  simp_rw [normUnitsEval]
  have t₀ := fun i ↦ hasFDeriv_normUnitsEvalSingle K i w c
  have := HasFDerivAt.finset_prod (u := Finset.univ) (fun i _ ↦ t₀ i)
  simp at this
  convert this
  · rw [← Finset.univ.mul_prod_erase _ (Finset.mem_univ w₀), Pi.smul_apply, smul_eq_mul]
    congr
    · rw [normUnitsEvalSingle, dif_pos rfl]
    · simp_rw [normUnitsEvalProd]
      rw [Finset.prod_subtype (Finset.univ.erase w₀) (p := fun w ↦ w ≠ w₀)]
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [normUnitsEvalSingle, dif_neg i.prop, Subtype.coe_eta, Pi.pow_apply]
      intro _
      simp_rw [Finset.mem_erase, Finset.mem_univ, and_true]
  · unfold jacobian
    rw [ContinuousLinearMap.proj_pi]
    unfold jacobianCoeff
    rw [Finset.smul_sum]
    refine Fintype.sum_congr _ _ ?_
    intro i
    by_cases hi : i = w₀
    · unfold normUnitsEvalSingle
      unfold FDeriv_normUnitsEvalSingle
      simp_rw [hi, dif_pos, one_smul]
      rw [Finset.prod_subtype (Finset.univ.erase w₀) (p := fun w ↦ w ≠ w₀)]
      simp_rw [Subtype.coe_eta, dite_eq_ite, ite_apply]
      rw [Finset.univ.prod_ite_of_false]
      rfl
      intro i _
      exact i.prop
      intro _
      simp_rw [Finset.mem_erase, Finset.mem_univ, and_true]
    · simp_rw [dif_neg hi]
      unfold FDeriv_normUnitsEvalSingle
      simp_rw [dif_neg hi]
      rw [show normUnits K ⟨i, hi⟩ w ^ c i = normUnitsEvalSingle K i c w by
        rw [normUnitsEvalSingle, dif_neg hi, Pi.pow_apply]]
      simp_rw [smul_smul, ← mul_assoc]
      rw [Finset.univ.prod_erase_mul]
      rw [prod_normUnitsEvalSingle_apply, normUnitsEval]
      congr 2
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      exact Finset.mem_univ _

open scoped Real

open ENNReal in
theorem volume_normLessOne :
    (volume (normLessThanOne K)).toReal =
      2 ^ NrRealPlaces K * π ^ NrComplexPlaces K * regulator K := by
  classical
  have hg₁ : 0 ≤ regulator K := le_of_lt (regulator_pos K)
  have hg₃ : 0 ≤ (finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have hg₄ : 0 ≤ (2 : ℝ)⁻¹ ^ NrComplexPlaces K := by
    refine pow_nonneg ?_ _
    exact inv_nonneg.mpr zero_le_two
  rw [volume_normLessThanOne, volume_normLessOne₀]
  rw [← (fusionEquiv_measure_preserving K).set_lintegral_comp_preimage]
  rw [show (fusionEquiv K) ⁻¹' normLessThanOne₁ K = normLessThanOne₂ K by rfl]
  rw [normLessThanOne₂_eq_image]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume _
    (fun c _ ↦ HasFDerivAt.hasFDerivWithinAt (hasFDeriv_normUnitsEval K c))]
  have h_rank : NrComplexPlaces K + rank K = finrank ℚ K - 1 := by
    rw [rank, ← Nat.add_sub_assoc NeZero.one_le, card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← card_add_two_mul_card_eq_rank]
    ring_nf
  have h_int : ∫⁻ x in S K, .ofReal (|x w₀| ^ (finrank ℚ K - 1)) = .ofReal (finrank ℚ K : ℝ)⁻¹ := by
    rw [volume_pi, ← lintegral_indicator _ (measurable_S K), lintegral_eq_lmarginal_univ 0,
      lmarginal_erase' _ ?_ (Finset.mem_univ w₀)]
    swap
    · refine Measurable.indicator ?_ (measurable_S K)
      refine Measurable.ennreal_ofReal ?_
      refine Measurable.pow_const ?_ _
      exact Measurable.norm (measurable_pi_apply w₀)
    have : ∀ x xᵢ,
        (S K).indicator
          (fun x ↦ ENNReal.ofReal (|x w₀| ^ (finrank ℚ K - 1))) (Function.update x w₀ xᵢ) =
        (Set.Ioc 0 1).indicator (fun x ↦ .ofReal  (x ^ (finrank ℚ K - 1))) xᵢ *
          (Set.univ.pi fun _ : { x // x ∈ Finset.univ.erase w₀ } ↦ Set.Ico 0 1).indicator 1
            (fun w ↦ x w.val) := by
      intro x xᵢ
      rw [Set.indicator_apply, Set.indicator_apply, Function.update_apply]
      split_ifs with h₁ h₂ h₃ h₄ h₅
      · rw [Set.indicator_of_mem, Pi.one_apply, mul_one, abs_eq_self.mpr h₃.1.le]
        intro w _
        dsimp
        simp only [S, Set.mem_pi, Set.mem_univ, true_implies] at h₁
        specialize h₁ w
        rwa [Function.update_apply, if_neg (Finset.mem_erase.mp w.prop).1,
          if_neg (Finset.mem_erase.mp w.prop).1] at h₁
      · exfalso
        simp [S] at h₁
        specialize h₁ w₀
        rw [Function.update_apply, if_pos rfl, if_pos rfl] at h₁
        exact h₃ h₁
      · simp [not_true_eq_false] at h₂
      · simp [not_true_eq_false] at h₂
      · simp [S, Set.mem_pi, Set.mem_univ, true_implies, Function.update_apply] at h₁
        obtain ⟨w, hw⟩ := h₁
        by_cases hw' : w = w₀
        · rw [if_pos hw', if_pos hw'] at hw
          exfalso
          exact hw h₅
        · rw [if_neg hw', if_neg hw'] at hw
          rw [Set.indicator_of_not_mem, mul_zero]
          simp_rw [Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, Finset.mem_erase,
            Finset.mem_univ, and_true, not_forall]
          exact ⟨w, hw', hw⟩
      · rw [zero_mul]
    simp_rw [this]
    have : ∀ c : InfinitePlace K → ℝ,
        ((Set.univ.pi fun _ : {x // x ∈ Finset.univ.erase w₀} ↦ Set.Ico 0 1).indicator
          1 fun w ↦ c w.val : ℝ≥0∞) ≠ ⊤ := by
      intro c
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    simp_rw [lintegral_mul_const' _ _ (this _), lintegral_indicator _ measurableSet_Ioc]
    have : ∫⁻ (x : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (x ^ (finrank ℚ K - 1)) =
        .ofReal (finrank ℚ K : ℝ)⁻¹ := by
      rw [← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le
        zero_le_one, integral_pow, one_pow, zero_pow (Nat.add_one_ne_zero _), sub_zero,
        Nat.cast_sub, Nat.cast_one,
        sub_add_cancel, one_div]
      · exact finrank_pos
      · change IntegrableOn (fun x ↦ x ^ (finrank ℚ K - 1)) _ _
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        exact intervalIntegral.intervalIntegrable_pow _
      · refine ae_le_of_ae_lt ?_
        rw [ae_restrict_iff_subtype measurableSet_Ioc]
        filter_upwards with ⟨a, ha⟩
        refine pow_pos  ha.1 _
    simp_rw [this, ← smul_eq_mul, ← Pi.smul_def]
    rw [lmarginal_const_smul]
    · rw [lmarginal]
      simp_rw [Function.updateFinset_def]
      conv_lhs =>
        enter [2, 2, y, 3, w]
        rw [dif_pos w.prop]
      rw [lintegral_indicator_one, Measure.pi_pi]
      simp_rw [Real.volume_Ico, sub_zero, ofReal_one, Finset.prod_const_one, mul_one]
      exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico
    · refine Measurable.indicator measurable_const ?_
      change MeasurableSet {i | _}
      refine MeasurableSet.congr (s := ⋂ w : {w // w ∈ Finset.univ.erase w₀},
        (Set.univ.pi fun z : InfinitePlace K ↦ if z = w.val then Set.Ico 0 1 else Set.univ)) ?_ ?_
        -- {i | i w.val ∈ Set.Ico 0 1}) ?_ ?_
      · refine  MeasurableSet.iInter fun _ ↦ ?_
        refine MeasurableSet.pi ?_ ?_
        exact Set.countable_univ
        intro _ _
        refine MeasurableSet.ite' ?_ ?_
        exact fun _ ↦ measurableSet_Ico
        exact fun _ ↦ MeasurableSet.univ
      · ext
        simp only [Set.mem_iInter, Set.mem_pi, Set.mem_univ, Set.mem_ite_univ_right, Set.mem_Ico,
          true_implies, forall_eq, Subtype.forall, Finset.mem_erase, ne_eq, Finset.mem_univ,
          and_true, Set.mem_setOf_eq]
  calc
    _ = 2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K *
          (∫⁻ x in S K, .ofReal |(jacobian K x).det| * .ofReal
            (∏ w : { w : InfinitePlace K // w.IsComplex }, |normUnitsEval K x w|)).toReal := by
      simp only [toReal_mul, toReal_pow, toReal_ofNat, coe_toReal, NNReal.coe_real_pi,
        coe_finset_prod, mul_assoc, ← norm_toNNReal, Real.norm_eq_abs, fusionEquiv_apply,
        ofReal_prod_of_nonneg (fun _ _ ↦ abs_nonneg _)]
      rfl
    _ = 2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K *
          (∫⁻ x in S K,
            .ofReal (2⁻¹ ^ NrComplexPlaces K * regulator K * finrank ℚ K) *
            (.ofReal ((∏ w : { w : InfinitePlace K // w.IsComplex },
              normUnitsEvalProd K (fun w ↦ x w) w)⁻¹) *
            .ofReal (∏ w : { w : InfinitePlace K // w.IsComplex },
              normUnitsEvalProd K (fun w ↦ x w) w) *
            .ofReal (|x w₀| ^
              (Fintype.card {w : InfinitePlace K // w.IsComplex} + rank K)))).toReal := by
      have hl₂ : ∀ (c : InfinitePlace K → ℝ) (w : {w : InfinitePlace K // w.IsComplex}),
          0 ≤ normUnitsEvalProd K (fun z ↦ c z) w.val := by
        intro _ _
        refine le_of_lt ?_
        exact normUnitsEvalProd_pos K _ _
      simp_rw [jacobian_det, normUnitsEval, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_eq_self.mpr (hl₂ _ _), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        pow_add]
      have hl₃ : ∀ x : InfinitePlace K → ℝ,
          0 ≤ (∏ w : {w : InfinitePlace K // w.IsComplex},
            normUnitsEvalProd K (fun w ↦ x ↑w) w.val)⁻¹ := by
        intro _
        rw [inv_nonneg]
        refine Finset.univ.prod_nonneg fun _ _ ↦ ?_
        refine le_of_lt ?_
        exact normUnitsEvalProd_pos K _ _
      have hl₄ : ∀ c : InfinitePlace K → ℝ, 0 ≤ |c w₀| ^ rank K := by
        intro _
        refine pow_nonneg (abs_nonneg _) _
      have hl₅ :  ∀ c : InfinitePlace K → ℝ,
          0 ≤ |c w₀| ^ Fintype.card {w : InfinitePlace K // w.IsComplex} := by
        intro _
        refine pow_nonneg (abs_nonneg _) _
      simp_rw [mul_assoc, ofReal_mul (hl₃ _), ofReal_mul hg₄, ofReal_mul (hl₄ _), ofReal_mul hg₃,
        ofReal_mul hg₁, ofReal_mul (hl₅ _)]
      congr; ext; ring
    _ =  2 ^ NrRealPlaces K *  π ^ NrComplexPlaces K * regulator K * 2 ^ NrComplexPlaces K *
          (2 ^ NrComplexPlaces K)⁻¹ * finrank ℚ K *
          (∫⁻ x in S K, .ofReal (|x w₀| ^ (finrank ℚ K - 1))).toReal := by
      rw [lintegral_const_mul' _ _ ofReal_ne_top, ofReal_mul (by positivity),
        ofReal_mul (by positivity)]
      have hl₂ : ∀ c : InfinitePlace K → ℝ, 0 <
          (∏ w : { w : InfinitePlace K // w.IsComplex }, normUnitsEvalProd K (fun w ↦ c w) w) := by
        intro _
        refine Finset.univ.prod_pos fun _ _ ↦ normUnitsEvalProd_pos K _ _
      have hl₃ : ∀ c : InfinitePlace K → ℝ,
          ENNReal.ofReal (∏ w : { w : InfinitePlace K // w.IsComplex },
            normUnitsEvalProd K (fun w ↦ c w) w) ≠ 0 := by
        intro _
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact hl₂ _
      have hl₄ : ∀ c : InfinitePlace K → ℝ,
          ENNReal.ofReal (∏ w : { w : InfinitePlace K // w.IsComplex },
            normUnitsEvalProd K (fun w ↦ c w) w) ≠ ⊤ := by
        intro _
        exact ENNReal.ofReal_ne_top
      simp_rw [toReal_mul, toReal_ofReal hg₁, toReal_ofReal hg₄, toReal_ofReal hg₃,
        ofReal_inv_of_pos (hl₂ _), ENNReal.inv_mul_cancel (hl₃ _) (hl₄ _), one_mul, mul_pow,
        inv_pow, ← mul_assoc, h_rank]
      congr 2
      ring
    _ = 2 ^ NrRealPlaces K * π ^ NrComplexPlaces K * regulator K := by
      rw [h_int, toReal_ofReal, mul_assoc, mul_inv_cancel, mul_one, mul_assoc, mul_inv_cancel,
        mul_one]
      · refine pow_ne_zero _ two_ne_zero
      · rw [Nat.cast_ne_zero]
        refine ne_of_gt ?_
        exact finrank_pos
      · rw [inv_nonneg]
        exact Nat.cast_nonneg _
  · exact normUnitsEval_injOn K
  · exact measurable_S K
  · exact measurableSet_normLessThanOne₁ K
  · refine Finset.univ.measurable_prod fun i _ ↦ ?_
    rw [measurable_coe_nnreal_ennreal_iff]
    refine Measurable.nnnorm ?_
    exact Measurable.comp (measurable_pi_apply _) measurable_snd

open Classical in
theorem volume_normEqOne :
    volume (normEqOne K) = 0 := by
  -- The sets `A n` are all subsets of `normLessThanOne` and their volume is some multiple
  -- of the volume of `normEqOne`. Since the corresponding series diverge if the volume
  -- of `normEqOne` is non-zero and `normLessThanOne` has finite volume since it is bounded,
  -- we get the result by contradiction.
  let A : ℕ → (Set (E K)) := fun n ↦ (1 - (n + 2 : ℝ)⁻¹) • normEqOne K
  have hn₀ : ∀ n : ℕ, 0 < 1 - (n + 2 : ℝ)⁻¹ := by
    intro n
    rw [sub_pos, inv_lt_one_iff]
    exact Or.inr (by linarith)
  have hn₁ : ∀ n : ℕ, 1 - (n + 2 : ℝ)⁻¹ ≤ 1 := by
    intro n
    refine (sub_le_self_iff _).mpr (by positivity)
  have hA₁ : ∀ n : ℕ, A n ⊆ normLessThanOne K := fun n ↦ smul_normEqOne_subset _ (hn₀ n) (hn₁ n)
  have hA₂ : ∀ n : ℕ, volume (A n) =
      ((1 - (n + 2 : ENNReal)⁻¹) ^ finrank ℚ K) * volume (normEqOne K) := fun n ↦ by
    rw [Measure.addHaar_smul, mixedEmbedding.finrank, abs_pow, ENNReal.ofReal_pow (abs_nonneg _),
      abs_eq_self.mpr (hn₀ n).le, ENNReal.ofReal_sub, ENNReal.ofReal_inv_of_pos,
      ENNReal.ofReal_add,
      ENNReal.ofReal_one, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    any_goals positivity
  have hA₃ : ∀ n, NullMeasurableSet (A n) := fun n ↦
    ((measurableSet_normEqOne K).const_smul₀  _).nullMeasurableSet
  have hA₄ : Pairwise (AEDisjoint volume on A) := fun n m hnm ↦ by
    suffices (1 - (n + 2 : ℝ)⁻¹) ^ finrank ℚ K ≠ (1 - (m + 2 : ℝ)⁻¹) ^ finrank ℚ K by
      refine Disjoint.aedisjoint ?_
      dsimp [A]
      rw [smul_normEqOne _ (hn₀ n), smul_normEqOne _ (hn₀ m)]
      refine Set.disjoint_iff_forall_ne.mpr fun _ hx _ hy hxy ↦ ?_
      rw [← hx.2, ← hy.2, ← hxy] at this
      exact this rfl
    rwa [ne_eq, ← Real.rpow_natCast, ← Real.rpow_natCast, Real.rpow_left_inj (hn₀ n).le (hn₀ m).le
      (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)), sub_right_inj, inv_eq_iff_eq_inv, inv_inv,
      add_left_inj, Nat.cast_inj]
  have hA₅ : volume (⋃ i, A i) ≤ volume (normLessThanOne K) := measure_mono (Set.iUnion_subset hA₁)
  have h : volume (normLessThanOne K) < ⊤ := (isBounded_normLessThanOne K).measure_lt_top
  contrapose! h
  refine (le_trans ?_ (tsum_meas_le_meas_iUnion_of_disjoint₀ volume hA₃ hA₄)).trans hA₅
  simp_rw [hA₂, top_le_iff, ENNReal.tsum_mul_right]
  refine ENNReal.mul_eq_top.mpr (Or.inr ⟨?_, h⟩)
  suffices Tendsto (fun n : ℕ ↦ (1 - (n + 2 : ENNReal)⁻¹) ^ finrank ℚ K) atTop (nhds 1) by
    by_contra! h
    exact zero_ne_one <| tendsto_nhds_unique (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h) this
  rw [show nhds (1 : ENNReal) = nhds ((1 - 0) ^ finrank ℚ K) by norm_num]
  refine ENNReal.Tendsto.pow <|
    ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp_rw [show ∀ n : ℕ, (n : ENNReal) + 2 = (n + 2 : ℕ) by exact fun _ ↦ by norm_cast]
  rw [Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ (n : ENNReal)⁻¹)]
  exact ENNReal.tendsto_inv_nat_nhds_zero

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
    simp_rw [integralPoint_torsionSMul_smul_coe, Submonoid.coe_mul, mul_smul]

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

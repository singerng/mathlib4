/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Topology.LocallyClosed
import Mathlib.NumberTheory.AbelSummation

/-!
# Docstring

-/

open Asymptotics Filter

theorem Asymptotics.isEquivalent_nat_floor {R : Type*} [NormedLinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    (fun (x : R) ↦ ↑⌊x⌋₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards with x hx
    rw [hx, Nat.floor_zero, Nat.cast_eq_zero]
  · exact tendsto_nat_floor_div_atTop

theorem Asymptotics.isEquivalent_nat_ceil {R : Type*} [NormedLinearOrderedField R]
    [OrderTopology R] [FloorRing R] :
    (fun (x : R) ↦ ↑⌈x⌉₊) ~[atTop] (fun x ↦ x) := by
  refine isEquivalent_of_tendsto_one ?_ ?_
  · filter_upwards with x hx
    rw [hx, Nat.ceil_zero, Nat.cast_eq_zero]
  · exact tendsto_nat_ceil_div_atTop

theorem isLocallyClosed_Icc {X : Type*} [TopologicalSpace X] [Preorder X] [OrderClosedTopology X]
    {a b : X} :
    IsLocallyClosed (Set.Icc a b) := by
  refine IsClosed.isLocallyClosed ?_
  exact isClosed_Icc

theorem isLocallyClosed_Ioo {X : Type*} [TopologicalSpace X] [LinearOrder X]
    [OrderClosedTopology X] {a b : X} :
    IsLocallyClosed (Set.Ioo a b) := by
  refine IsOpen.isLocallyClosed ?_
  exact isOpen_Ioo

theorem isLocallyClosed_Ici {X : Type*} [TopologicalSpace X] [Preorder X] [ClosedIciTopology X]
    {a : X} :
    IsLocallyClosed (Set.Ici a) := by
  refine IsClosed.isLocallyClosed ?_
  exact isClosed_Ici

theorem isLocallyClosed_Iic {X : Type*} [TopologicalSpace X] [Preorder X] [ClosedIicTopology X]
    {a : X} :
    IsLocallyClosed (Set.Iic a) := by
  refine IsClosed.isLocallyClosed ?_
  exact isClosed_Iic

theorem isLocallyClosed_Ioi {X : Type*} [TopologicalSpace X] [LinearOrder X] [ClosedIicTopology X]
    {a : X} :
    IsLocallyClosed (Set.Ioi a) := by
  refine IsOpen.isLocallyClosed ?_
  exact isOpen_Ioi

theorem isLocallyClosed_Iio {X : Type*} [TopologicalSpace X] [LinearOrder X] [ClosedIciTopology X]
    {a : X} :
    IsLocallyClosed (Set.Iio a) := by
  refine IsOpen.isLocallyClosed ?_
  exact isOpen_Iio

theorem isLocallyClosed_Ioc {X : Type*} [TopologicalSpace X] [LinearOrder X]
    [OrderClosedTopology X] (a b : X) :
    IsLocallyClosed (Set.Ioc a b) := by
  rw [← Set.Iic_inter_Ioi]
  refine IsLocallyClosed.inter ?_ ?_
  · exact isLocallyClosed_Iic
  · exact isLocallyClosed_Ioi

theorem isLocallyClosed_Ico {X : Type*} [TopologicalSpace X] [LinearOrder X]
    [OrderClosedTopology X] (a b : X) :
    IsLocallyClosed (Set.Ico a b) := by
  rw [← Set.Iio_inter_Ici]
  refine IsLocallyClosed.inter ?_ ?_
  · exact isLocallyClosed_Iio
  · exact isLocallyClosed_Ici

noncomputable section

open Finset intervalIntegral MeasureTheory IntervalIntegrable

variable {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜}

open Filter Topology

theorem integral_repr (f : ℕ → ℂ) (hf : f 0 = 0) (s : ℂ) (hs : 1 < s.re)
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℂ))
    (hLS : LSeriesSummable f s) :
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / ↑t ^ (s + 1)) := by
  have hnz : s ≠ 0 := by
    contrapose! hs
    rw [hs, Complex.zero_re]
    exact zero_le_one
  have hderiv : ∀ x ≠ 0, deriv (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x = (- s) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    have := (hasDerivAt_ofReal_cpow (r := - s - 1) hx ?_).deriv
    rw [sub_add_cancel, deriv_div_const, div_neg, ← neg_div, div_eq_iff, neg_eq_iff_eq_neg] at this
    rw [this]
    ring
    · exact hnz
    · rw [ne_eq, sub_eq_neg_self, neg_eq_zero]
      exact hnz
  have h1 : ∀ n,  ∑ k in range (n + 1), LSeries.term f s k =
      ∑ k ∈ Icc 0 ⌊(n : ℝ)⌋₊, ↑k ^ (- s) * f k := by
    intro n
    rw [Nat.floor_natCast, ← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [LSeries.term]
    split_ifs with hk
    · rw [hk, hf, mul_zero]
    · rw [Complex.cpow_neg]
      ring
  have h2 :
      Tendsto (fun n ↦ ∑ k in range (n + 1), LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hLS.hasSum.tendsto_sum_nat
  have h3 := fun n : ℕ ↦ sum_mul_eq_sub_integral_mul' f
    (f := fun x : ℝ ↦ ↑x ^ (- s)) (b := n) hf ?_ ?_
  · have h4 : Tendsto (fun n : ℕ ↦ ↑n ^ (- s) * ∑ k ∈ Icc 0 ⌊(n : ℝ)⌋₊, f k) atTop (𝓝 0) := by
      simp only [Nat.floor_natCast]
      have : (fun n : ℕ ↦ n ^ (-s) * ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℂ) ^ (- s + 1) := by
        have := Asymptotics.IsBigO.mul
          (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℂ) ^ (-s)) atTop) hO
        refine Asymptotics.IsBigO.congr' this ?_ ?_
        · exact Eq.eventuallyEq rfl
        · filter_upwards [eventually_ne_atTop 0] with n hn
          rw [Complex.cpow_add, Complex.cpow_one]
          exact Nat.cast_ne_zero.mpr hn
      refine Asymptotics.IsBigO.trans_tendsto this ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-s.re + 1)) atTop (𝓝 0) := by
        rw [show -s.re + 1 = - (s.re - 1) by rw [neg_sub', sub_neg_eq_add]]
        refine (tendsto_rpow_neg_atTop ?_).comp tendsto_natCast_atTop_atTop
        rwa [sub_pos]
      refine Tendsto.congr' ?_ this
      filter_upwards with n
      rw [Complex.norm_natCast_cpow_of_re_ne_zero, Complex.add_re, Complex.neg_re, Complex.one_re]
      rw [Complex.add_re, Complex.neg_re, Complex.one_re, ne_eq]
      rw [neg_add_eq_iff_eq_add, add_zero]
      exact hs.ne
    have h5 : Tendsto (fun n : ℕ ↦
        ∫ (t : ℝ) in Set.Ioc 1 (n : ℝ),
          deriv (fun x : ℝ ↦ (x : ℂ) ^ (- s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k)
            atTop (𝓝 (∫ (t : ℝ) in Set.Ioi 1, deriv (fun x : ℝ ↦ (x : ℂ) ^ (- s)) t *
              (∑ k ∈ Icc 0 ⌊t⌋₊, f k))) := by
      refine Tendsto.congr' (by
            filter_upwards [eventually_ge_atTop 1] with n hn
            rw [← integral_of_le (Nat.one_le_cast.mpr hn)]) ?_
      refine intervalIntegral_tendsto_integral_Ioi 1 ?_ tendsto_natCast_atTop_atTop
      refine IntegrableOn.congr_fun ?_
        (fun x hx ↦ by
          rw [hderiv]
          exact (zero_lt_one.trans hx).ne') measurableSet_Ioi
      simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      refine IntegrableOn.integrable ?_
      have h : (fun x : ℝ ↦ ∑ k ∈ Icc 0 ⌊x⌋₊, f k) =O[atTop] fun x ↦ ↑x := by
        have : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop := by
          exact tendsto_nat_floor_atTop
        have := Asymptotics.IsBigO.comp_tendsto hO this
        simp [Function.comp_def] at this
        refine Asymptotics.IsBigO.trans this ?_
        have := (Asymptotics.isEquivalent_nat_floor (R := ℝ)).isBigO
        rw [← Asymptotics.isBigO_norm_left]
        simp only [Complex.norm_natCast]
        exact this
      rw [Asymptotics.isBigO_iff] at h
      obtain ⟨C, hC⟩ := h
      rw [← integrableOn_Ici_iff_integrableOn_Ioi]
      refine LocallyIntegrableOn.integrableOn_of_isBigO_atTop
        (g := fun x : ℝ ↦ (x : ℂ) ^ (- s - 1 + 1)) ?_ ?_ ?_
      · refine LocallyIntegrableOn.continuousOn_mul ?_ ?_ ?_
        · rw [locallyIntegrableOn_iff]
          · intro K hK₁ hK₂
            have : K ⊆ Set.Icc (sInf K) (sSup K) := by
              refine Bornology.IsBounded.subset_Icc_sInf_sSup ?_
              exact IsCompact.isBounded hK₂
            refine IntegrableOn.mono_set ?_ this
            convert abelSummationProof.integrablemulsum f (fun _ ↦ 1) (a := sInf K) (b := sSup K)
              ?_ ?_
            · rw [one_mul]
            · refine Real.sInf_nonneg ?_
              intro x hx
              have := hK₁ hx
              exact zero_le_one.trans this
            · rw [integrableOn_const]
              right
              exact measure_Icc_lt_top
          · exact isLocallyClosed_Ici
        · refine ContinuousOn.cpow_const ?_ ?_
          · refine Continuous.continuousOn ?_
            exact Complex.continuous_ofReal
          · intro x hx
            rw [Complex.ofReal_mem_slitPlane]
            exact zero_lt_one.trans_le hx
        · exact isLocallyClosed_Ici
      · rw [Asymptotics.isBigO_iff]
        use C
        filter_upwards [hC, eventually_ne_atTop 0] with x hx₁ hx₂
        rw [Complex.cpow_add, norm_mul, norm_mul, mul_left_comm, Complex.cpow_one,
          Complex.norm_real]
        · refine mul_le_mul_of_nonneg_left hx₁ ?_
          exact norm_nonneg _
        exact Complex.ofReal_ne_zero.mpr hx₂
      · refine ⟨Set.Ioi 1, ?_, ?_⟩
        · exact Ioi_mem_atTop 1
        · rw [integrableOn_Ioi_cpow_iff]
          · simp [hs]
          · exact zero_lt_one
    have h6 : - ∫ (t : ℝ) in Set.Ioi 1, deriv (fun x : ℝ ↦ (x : ℂ) ^ (- s)) t *
        (∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
        s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / ↑t ^ (s + 1)) := by
      rw [← integral_mul_left, ← MeasureTheory.integral_neg]
      refine integral_congr_ae ?_
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx ↦ ?_
      rw [hderiv, ← neg_add', Complex.cpow_neg]
      ring
      exact (zero_lt_one.trans hx).ne'
    · rw [← h6]
      have h7 := Tendsto.sub h4 h5
      rw [zero_sub] at h7
      refine tendsto_nhds_unique h2 (Tendsto.congr ?_ h7)
      intro n
      rw [h1]
      specialize h3 n
      erw [h3]
      rfl
  · intro t ht
    refine DifferentiableAt.comp (𝕜 := ℝ) t (f := Complex.ofReal) (g := fun z : ℂ ↦ z ^ (-s)) ?_ ?_
    · have : DifferentiableAt ℂ (fun z : ℂ ↦ z ^ (- s)) t := by
        refine DifferentiableAt.cpow ?_ ?_ ?_
        exact differentiableAt_id
        exact differentiableAt_const _
        refine Complex.ofReal_mem_slitPlane.mpr ?_
        exact lt_of_lt_of_le zero_lt_one ht.1
      exact this.restrictScalars ℝ
    · refine Differentiable.differentiableAt ?_
      exact Complex.ofRealCLM.differentiable.restrictScalars ℝ
  · refine IntegrableOn.congr_fun (f := fun x ↦ -s * ↑x ^ (-s - 1)) ?_ ?_ measurableSet_Icc
    · refine Integrable.const_mul ?_ _
      refine IntegrableOn.integrable ?_
      refine ContinuousOn.integrableOn_Icc ?_
      refine ContinuousOn.cpow_const ?_ ?_
      · exact Complex.continuous_ofReal.continuousOn
      · intro x hx
        rw [Complex.ofReal_mem_slitPlane]
        exact zero_lt_one.trans_le hx.1
    · intro x hx
      dsimp only
      rw [hderiv]
      exact (zero_lt_one.trans_le hx.1).ne'

variable (f : ℕ → ℂ) (l : ℂ)
  (hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 0 n, f k : ℂ) / n) atTop (𝓝 l))

include hlim

theorem lemma1 :
    Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 0 ⌊t⌋₊, f k : ℂ) / t) atTop (𝓝 l) := by
  have lim1 : Tendsto (fun t : ℝ ↦ (∑ k ∈ Icc 0 ⌊t⌋₊, f k : ℂ) / ⌊t⌋₊) atTop (𝓝 l) :=
    Tendsto.comp hlim (tendsto_nat_floor_atTop (α := ℝ))
  have lim2 : Tendsto (fun t : ℝ ↦ ↑(⌊t⌋₊ / t : ℝ)) atTop (𝓝 (1 : ℂ)) := by
    rw [← Complex.ofReal_one]
    rw [tendsto_ofReal_iff]
    exact tendsto_nat_floor_div_atTop
  have lim3 := Tendsto.mul lim1 lim2
  rw [mul_one] at lim3
  refine Tendsto.congr' ?_ lim3
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [Complex.ofReal_div, Complex.ofReal_natCast, div_mul_div_cancel₀]
  rw [Nat.cast_ne_zero, ne_eq, Nat.floor_eq_zero, not_lt]
  exact ht

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ‖∑ k ∈ Icc 0 ⌊t⌋₊, f k - l * t‖ < ε * t := by
  rw [Metric.tendsto_nhds] at hlim
  specialize this ε hε
  filter_upwards [eventually_gt_atTop 0, this] with t ht₁ ht₂
  rwa [← div_lt_iff₀, ← Real.norm_of_nonneg (r := t), ← Complex.norm_real, ← norm_div,
    Complex.norm_real, Real.norm_of_nonneg (r := t), sub_div, mul_div_cancel_right₀]
  · exact_mod_cast ht₁.ne'
  · exact ht₁.le
  · exact ht₁.le
  · exact ht₁

#where

#exit

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ‖S f t - l * t‖ ≤ ε := sorry

theorem final_step1 (s : ℝ) (ε : ℝ) :
    ∃ c, ‖(LSeries f s) / s - l / (s - 1)‖ ≤ ε / (s - 1) + c := sorry

theorem final_step2 (ε : ℝ) (hε : 0 < ε) :
    limsup (fun s : ℝ ↦ ‖(s - 1) * LSeries f s - l‖) (𝓝[<] 1) ≤ ε := sorry

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := sorry

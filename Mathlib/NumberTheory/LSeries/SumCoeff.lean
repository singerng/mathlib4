/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
  # Docs
-/


section

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

end

open Finset Filter MeasureTheory Topology

private theorem aux1 {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (deriv fun (t : ℝ) ↦ (t : ℂ) ^ (-s)) (Set.Ici 1) := by
  have h_int : IntegrableOn (fun x ↦ Complex.abs (-s) * x ^ (-s - 1).re) (Set.Ici 1) := by
    refine Integrable.const_mul (integrableOn_Ici_iff_integrableOn_Ioi.mpr
      ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr ?_)) _
    rwa [Complex.sub_re, Complex.neg_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel,
      neg_lt_zero]
  refine (integrable_norm_iff (aestronglyMeasurable_deriv _ _)).mp <|
    h_int.congr_fun  (fun t ht ↦ ?_) measurableSet_Ici
  rw [Complex.norm_eq_abs, Complex.deriv_cpow_const' (zero_lt_one.trans_le ht).ne'
    (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)), map_mul,
    Complex.abs_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht)]

private theorem aux2 (f : ℕ → ℂ) (hf₀ : f 0 = 0) (s : ℂ) (n : ℕ) :
    ∑ k in range (n + 1), LSeries.term f s k = ∑ k ∈ Icc 0 n, ↑k ^ (- s) * f k := by
  rw [← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain hk | rfl := ne_or_eq k 0
  · rw [LSeries.term_of_ne_zero hk, Complex.cpow_neg, mul_comm, div_eq_mul_inv]
  · rw [LSeries.term_zero, hf₀, mul_zero]

private theorem aux3 {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hbO : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    (fun t : ℝ ↦ ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop] fun t : ℝ ↦ t ^ r := by
  refine (Asymptotics.IsBigO.comp_tendsto hbO tendsto_nat_floor_atTop).trans <|
    (Asymptotics.isEquivalent_nat_floor).isBigO.rpow hr ?_
  filter_upwards [eventually_ge_atTop 0] with _ ht using ht

private theorem aux4 (f g : ℝ → ℂ) (r s : ℝ) (hf : f =O[atTop] fun t ↦ t ^ r)
    (hf : g =O[atTop] fun t ↦ t ^ s) :
    (f * g : ℝ → ℂ) =O[atTop] fun t ↦ t ^ (r + s) := by
  sorry


theorem integral_repr (f : ℕ → ℂ)
    (hf₀ : f 0 = 0)
    {r : ℝ} (hr : 0 ≤ r)
    (s : ℂ)
    (hs : r < s.re)
    (hLS : LSeriesSummable f s)
    (hbO : (fun n ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hLS.hasSum.tendsto_sum_nat) ?_
  simp_rw [aux2 f hf₀ s]
  have h_lim : Tendsto (fun n : ℕ ↦ (fun t : ℝ ↦ (t : ℂ) ^ (-s)) ↑n * ∑ k ∈ Icc 0 n, f k)
      Filter.atTop (nhds 0) := by
    have : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (- (s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
    refine Asymptotics.IsBigO.trans_tendsto ?_ this
    rw [neg_sub]
    sorry
  have h_bigO : (fun t : ℝ ↦ deriv (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =O[atTop]
      fun t ↦ t ^ (r - s.re - 1) := by
    have := aux3 hr hbO
    rw [show r - s.re - 1 = ((-s).re - 1 + r) by rw [Complex.neg_re]; ring]
    refine aux4 _ _ _ _ ?_ this
    exact isBigO_deriv_cpow_const_atTop (-s)
  convert (tendsto_sum_mul_atTop_eq_sub_integral₀ f hf₀ ?_ (aux1 (hr.trans_lt hs)) h_lim h_bigO ?_)
    using 2
  · rw [← integral_mul_left, zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [Complex.deriv_cpow_const']
    · ring
    · exact (zero_lt_one.trans ht).ne'
    · exact (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos (hr.trans_lt hs)))
  · exact fun _ h ↦ differentiableAt_id.cpow_const'
      (zero_lt_one.trans_le h).ne' (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos (hr.trans_lt hs)))
  · exact ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)⟩

-- (deriv fun t ↦ ‖(fun t ↦ ↑t ^ (-s)) t‖)

theorem summable_of_abel (f : ℕ → ℂ)
    {r : ℝ}
    (s : ℂ)
    (hs : r < s.re)
    :
    LSeriesSummable f s := by
  rw [LSeriesSummable]
  refine Summable.congr_atTop (f₁ := fun n ↦ (n : ℂ) ^ (-s) * (f n)) ?_ ?_
  · refine summable_mul_of_bigO_atTop₀ f ?_ (f := fun t ↦ (t : ℂ) ^ (-s))
      ?_ ?_ ?_ (g := fun t ↦ t ^ (r - s.re - 1)) ?_ ?_
    · 

      -- refine DifferentiableAt.norm ℂ ?_ ?_
      -- refine DifferentiableAt.cpow_const' ?_ ?_ ?_
      have : DifferentiableAt ℝ (fun x ↦ x ^ (-s.re)) t := sorry
      refine DifferentiableAt.congr_of_eventuallyEq this ?_
      filter_upwards with x
      rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_nonneg, Complex.neg_re]


      sorry
    · sorry
    · sorry
    · sorry
    · exact ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)⟩
  · filter_upwards [eventually_ne_atTop 0] with n hn
    rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv, mul_comm]

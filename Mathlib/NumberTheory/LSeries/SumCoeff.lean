/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.NumberTheory.LSeries.Dirichlet

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

theorem integral_repr (f : ℕ → ℂ)
    {r : ℝ} (hr : 0 ≤ r)
    (s : ℂ)
    (hs : r < s.re)
    (hLS : LSeriesSummable f s)
    (hbO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (- s - 1) := by
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have h_fg : ∀ {n : ℕ}, n ≠ 0 → f n = g n := fun h ↦ by simp only [g, if_neg h]
  have h_g₀ : g 0 = 0 := by simp only [reduceIte, g]
  have h_sum : ∀ n, ∑ k ∈ Icc 0 n, g k = ∑ k ∈ Icc 1 n, f k := by
    intro n
    rw [← Nat.Icc_insert_succ_left n.zero_le, sum_insert, h_g₀, zero_add, zero_add,
      sum_congr rfl (fun _ h ↦ by rw [← h_fg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne'])]
    simp only [mem_Icc, not_and, zero_add, nonpos_iff_eq_zero, one_ne_zero, false_implies]
  have h_lim : Tendsto (fun n : ℕ ↦ (n : ℂ) ^ (-s) * ∑ k ∈ Icc 0 n, g k)
      Filter.atTop (nhds 0) := by
    have : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (- (s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp tendsto_natCast_atTop_atTop
    refine Asymptotics.IsBigO.trans_tendsto ?_ this
    rw [neg_sub]
    have : (fun n : ℕ ↦ (n : ℂ) ^ (- s)) =O[atTop] fun n ↦ (n : ℝ) ^ (- s.re) := by
      rw [Asymptotics.isBigO_iff]
      use 1
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Complex.norm_natCast_cpow_of_pos, Real.norm_rpow_of_nonneg, Real.norm_natCast,
        Complex.neg_re, one_mul]
      exact n.cast_nonneg
      exact hn
    have := Asymptotics.IsBigO.mul this hbO
    simp_rw [← h_sum] at this
    refine Asymptotics.IsBigO.congr' this ?_ ?_
    exact EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.rpow_add, neg_add_eq_sub]
    exact Nat.cast_pos.mpr hn
  have h_bigO : (fun t : ℝ ↦ deriv (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, g k) =O[atTop]
      fun t ↦ t ^ (r - s.re - 1) := by
    have : (fun n ↦ ∑ k ∈ Icc 0 n, g k) =O[atTop] fun n ↦ (n : ℝ) ^ r := by
      simp_rw [h_sum]
      exact hbO
    have := aux3 hr this
    rw [show r - s.re - 1 = ((-s).re - 1 + r) by rw [Complex.neg_re]; ring]
    refine Asymptotics.IsBigO.congr'
      (Asymptotics.IsBigO.mul (isBigO_deriv_cpow_const_atTop (-s)) this) ?_ ?_
    exact EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx]
  rw [LSeries_congr s h_fg]
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr
    ((LSeriesSummable_congr s h_fg).mp hLS).hasSum.tendsto_sum_nat) ?_
  convert (tendsto_sum_mul_atTop_eq_sub_integral₀ g _ ?_ (aux1 (hr.trans_lt hs)) h_lim h_bigO ?_)
    using 2
  · exact aux2 _ h_g₀ _ _
  · rw [← integral_mul_left, zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [Complex.deriv_cpow_const', neg_mul, neg_mul, neg_neg, mul_right_comm, mul_assoc, h_sum]
    · exact (zero_lt_one.trans ht).ne'
    · exact (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos (hr.trans_lt hs)))
  · exact h_g₀
  · exact fun _ h ↦ differentiableAt_id.cpow_const'
      (zero_lt_one.trans_le h).ne' (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos (hr.trans_lt hs)))
  · exact ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)⟩

example (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ⌊t⌋₊ / (t : ℂ) ^ (s + 1) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  rw [integral_repr _ zero_le_one s hs (LSeriesSummable_one_iff.mpr hs)]
  · rw [mul_right_inj' (Complex.ne_zero_of_one_lt_re hs)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp_rw [Pi.one_apply, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one,
      div_eq_mul_inv, ← Complex.cpow_neg, neg_add']
  · simp_rw [Real.rpow_one]
    refine Eventually.isBigO ?_
    filter_upwards with n using by simp


-- (deriv fun t ↦ ‖(fun t ↦ ↑t ^ (-s)) t‖)

theorem summable_of_abel (f : ℕ → ℂ)
    {r : ℝ}
    (s : ℂ)
    (hs : r < s.re)
    :
    LSeriesSummable f s := by
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have h_fg : ∀ {n : ℕ}, n ≠ 0 → f n = g n := fun h ↦ by simp only [g, if_neg h]
  have h_g₀ : g 0 = 0 := by simp only [g, reduceIte]
  rw [LSeriesSummable_congr s h_fg]
  refine Summable.congr_atTop (f₁ := fun n ↦ (n : ℂ) ^ (-s) * (g n)) ?_ ?_
  · refine summable_mul_of_bigO_atTop₀ g ?_ (f := fun t ↦ (t : ℂ) ^ (-s))
      ?_ ?_ ?_ (g := fun t ↦ t ^ (r - s.re - 1)) ?_ ?_
    · exact h_g₀
    · intro t ht
      · refine DifferentiableAt.norm ℂ ?_ ?_
        refine DifferentiableAt.cpow_const' ?_ ?_ ?_
        · exact differentiableAt_id
        · sorry
        · sorry
        refine (Complex.cpow_ne_zero ?_).mpr ?_
        · sorry
        · sorry
    ·
      sorry
    ·
      sorry
    ·
      sorry
    · exact ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)⟩
  · filter_upwards [eventually_ne_atTop 0] with n hn
    rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv, mul_comm]

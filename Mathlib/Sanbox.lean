import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

open Finset Filter Topology MeasureTheory

theorem integral_repr (f : ℕ → ℂ) (hf : f 0 = 0) (s : ℂ) (hs : 1 < s.re) {r : ℝ}
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r)
    (hLS : LSeriesSummable f s) :
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) * ↑t ^ (- s - 1)) := by
  have hnz : s ≠ 0 := by
    contrapose! hs
    rw [hs, Complex.zero_re]
    exact zero_le_one
  have hderiv : ∀ x ≠ 0, deriv (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x = (- s) * (x : ℂ) ^ (-s - 1) := by
    intro x hx
    refine Complex.deriv_cpow_const' (c := -s) hx ?_
    rwa [neg_ne_zero]
  have h1 : ∀ n,  ∑ k in range (n + 1), LSeries.term f s k =
      ∑ k ∈ Icc 0 n, ↑k ^ (- s) * f k := by
    intro n
    rw [← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [LSeries.term]
    split_ifs with hk
    · rw [hk, hf, mul_zero]
    · rw [Complex.cpow_neg]
      ring
  have h2 : Tendsto (fun n ↦ ∑ k in range (n + 1), LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hLS.hasSum.tendsto_sum_nat
  simp_rw [h1] at h2
  have := tendsto_sum_mul_atTop_sub_integral₀ f (f := fun t : ℝ ↦ (t : ℂ)^ (- s)) (l := 0)
    ?_ ?_ ?_ ?_ (g := fun t : ℝ ↦ t ^ (r - s.re)) ?_ ?_
  · have := tendsto_nhds_unique h2 this
    rw [this, zero_sub, ← integral_neg, ← integral_mul_left]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    dsimp only
    rw [hderiv, neg_mul, neg_mul, neg_neg]
    · ring
    · sorry
  · exact hf
  · intro t ht
    refine DifferentiableAt.comp (𝕜 := ℝ) (f := Complex.ofReal) (g := fun z : ℂ ↦ z ^ (-s)) t ?_ ?_
    · refine DifferentiableAt.restrictScalars ℝ (𝕜' := ℂ) (E := ℂ) (F := ℂ) ?_
      refine DifferentiableAt.cpow_const ?_ ?_
      · exact differentiableAt_id
      · rw [Complex.ofReal_mem_slitPlane]
        sorry
    · exact (Complex.ofRealCLM.differentiable.restrictScalars ℝ).differentiableAt
  · sorry
  · sorry
  · sorry
  · sorry

theorem summabllle (f : ℕ → ℂ) (hf : f 0 = 0) (s : ℂ) {r : ℝ} (hs : r < s.re)
    (hO : (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeriesSummable f s := by
  simp_rw [LSeriesSummable]
  convert_to Summable fun k ↦ k ^ (- s) * f k
  · ext
    rw [LSeries.term]
    split_ifs with hk
    · rw [hk, hf, mul_zero]
    · rw [Complex.cpow_neg]
      ring
  · refine toto f (f := fun t ↦ (t : ℂ) ^ (- s)) (g := 1) ?_ ?_ ?_ ?_  ?_
    · intro t ht
      refine DifferentiableAt.norm ℝ ?_ ?_
      · sorry
      · rw [Complex.cpow_ne_zero]
        · sorry
        · sorry
    · rw [IntegrableOn]
      sorry
    · have : (fun n : ℕ ↦ ‖(fun t : ℝ ↦ (t : ℂ) ^ (-s)) n‖) =O[atTop]
          fun n ↦ (n : ℝ) ^ (- s.re) := by
        sorry
      have := this.mul hO
      refine this.trans ?_
      refine Tendsto.isBigO_one (c := 0) _ ?_
      have := (tendsto_rpow_neg_atTop (y := s.re - r) ?_).comp tendsto_natCast_atTop_atTop
      · refine this.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [neg_sub, sub_eq_add_neg, Function.comp_apply, Real.rpow_add, mul_comm]
        exact Nat.cast_pos.mpr hn
      · linarith
    · have t1 :
          (fun t ↦ |deriv (fun t ↦ ‖(fun t : ℝ ↦ (t : ℂ) ^ (-s)) t‖) t|) =ᶠ[atTop]
            fun t ↦ s.re * t ^ (-s.re - 1) := by
        filter_upwards [eventually_ne_atTop 0] with t ht
        simp_rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_nonneg sorry sorry]
        rw [deriv_rpow_const]
        · simp
          sorry
        · exact differentiableAt_id
        · left
          exact ht
      have := t1.mul (EventuallyEq.refl _ fun t ↦ ∑ k ∈ Icc 0 ⌊t⌋₊, ‖f k‖)
      -- isBigO_deriv_rpow_const_atTop
      sorry
    · sorry

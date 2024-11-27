/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Docstring

-/

noncomputable section

open Finset intervalIntegral MeasureTheory IntervalIntegrable

variable {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜}

theorem sum_mul_eq_sub_integral_mul' (hc : c 0 = 0) (b : ℝ)
     (hf_diff : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ f t)
     (hf_int : IntegrableOn (deriv f) (Set.Icc 1 b)) :
     ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
       f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 1 b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  sorry

open Filter Topology


theorem integral_repr (f : ℕ → ℂ) (s : ℂ) :
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / t ^ (s + 1)) := by
  have hs : LSeriesSummable f s := sorry
  let g : ℕ → ℂ := fun k ↦ if k = 0 then 0 else f k
  have : ∀ n,  ∑ k in range (n + 1), LSeries.term f s k =
      ∑ k ∈ Icc 0 ⌊(n : ℝ)⌋₊, 1 / ↑↑k ^ s * g k := by
    intro n
    rw [Nat.floor_natCast, ← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : k = 0
    · simp only [LSeries.term, g, if_pos hk, mul_zero]
    · simp only [LSeries.term, g, if_neg hk, mul_comm, mul_one_div, Complex.ofReal_natCast]
  have t₃ : Tendsto (fun n ↦ ∑ k in range n, LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    hs.hasSum.tendsto_sum_nat

  have t₁ := fun n : ℕ ↦ sum_mul_eq_sub_integral_mul' g
    (f := fun x ↦ 1 / x ^ s) (b := n) (by simp [g]) sorry sorry
  have t₂ : (fun n ↦ ∑ k ∈ range n, LSeries.term f s k) =ᶠ[atTop]
     fun n ↦ (∑ k ∈ Icc 0 ⌊(n : ℝ)⌋₊, (k : ℝ) ^ (-s) * if k = 0 then 0 else f k) := sorry
  have t₃ : Tendsto (fun n ↦ ∑ k in range n, LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    HasSum.tendsto_sum_nat ?_
  have t₄ := t₃.congr' t₂
  simp_rw [t₁] at t₄
  have t₅ : Tendsto (fun n : ℕ ↦ s * ∫ (t : ℝ) in Set.Ioc 1 (n : ℝ),
    (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / t ^ (s + 1)) atTop
    (𝓝 (s * ∫ (t : ℝ) in Set.Ioi 1, (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / ↑t ^ (s + 1))) := sorry
  refine tendsto_nhds_unique_of_eventuallyEq t₄ t₅ ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  simp_rw [if_neg sorry]

  sorry

#exit

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ‖S f t - l * t‖ ≤ ε := sorry

theorem final_step1 (s : ℝ) (ε : ℝ) :
    ∃ c, ‖(LSeries f s) / s - l / (s - 1)‖ ≤ ε / (s - 1) + c := sorry

theorem final_step2 (ε : ℝ) (hε : 0 < ε) :
    limsup (fun s : ℝ ↦ ‖(s - 1) * LSeries f s - l‖) (𝓝[<] 1) ≤ ε := sorry

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := sorry

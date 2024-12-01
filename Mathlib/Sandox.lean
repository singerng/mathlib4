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


theorem integral_repr (f : ℕ → ℂ) (hf : f 0 = 0) (s : ℝ) :
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / (t ^ (s + 1) : ℝ)) := by
  have hS : (fun n : ℕ ↦ ∑ x ∈ Icc 0 n, f x) =O[atTop] fun n ↦ (n : ℂ) := sorry
  have hs : LSeriesSummable f s := sorry
  have h1 : ∀ n,  ∑ k in range (n + 1), LSeries.term f s k =
      ∑ k ∈ Icc 0 ⌊(n : ℝ)⌋₊, (k ^ (- s) : ℝ) * f k := by
    intro n
    rw [Nat.floor_natCast, ← Nat.Ico_zero_eq_range, Nat.Ico_succ_right]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [LSeries.term]
    split_ifs with hk
    · rw [hk, hf, mul_zero]
    · rw [mul_comm, mul_one_div, Complex.ofReal_cpow k.cast_nonneg, Complex.ofReal_natCast]
  have h2 :
      Tendsto (fun n ↦ ∑ k in range (n + 1), LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hs.hasSum.tendsto_sum_nat
  have h3 := fun n : ℕ ↦ sum_mul_eq_sub_integral_mul' f
    (f := fun x : ℝ ↦ (x ^ (- s) : ℝ)) (b := n) hf sorry sorry
  have h4 : Tendsto (fun n : ℕ ↦ (n ^ (- s) : ℝ) * ∑ k ∈ Icc 0 ⌊(n : ℝ)⌋₊, f k) atTop (𝓝 0) := by
    simp only [Nat.floor_natCast]
    sorry
  have h5 : Tendsto (fun n : ℕ ↦
      ∫ (t : ℝ) in Set.Ioc 1 (n : ℝ), deriv (fun x : ℝ ↦ ↑(x ^ (- s) : ℝ)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k)
      atTop (𝓝 (∫ (t : ℝ) in Set.Ioi 1, deriv (fun x : ℝ ↦ ↑(x ^ (- s) : ℝ)) t *
        (∑ k ∈ Icc 0 ⌊t⌋₊, f k))) := by
    sorry
  have h6 : - ∫ (t : ℝ) in Set.Ioi 1, deriv (fun x : ℝ ↦ ↑(x ^ (- s) : ℝ)) t *
      (∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / (t ^ (s + 1) : ℝ)) := by

    sorry
  rw [← h6]
  have h7 := Tendsto.sub h4 h5
  rw [zero_sub] at h7
  refine tendsto_nhds_unique h2 (Tendsto.congr ?_ h7)
  intro n
  rw [h1]
  specialize h3 n
  rw [h3]





  #exit

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

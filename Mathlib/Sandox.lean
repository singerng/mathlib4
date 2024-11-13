/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Docstring

-/

noncomputable section

open Filter Topology Finset Asymptotics Metric

variable (f : ℕ → ℂ) {l : ℝ}

abbrev S : ℝ → ℂ := fun t ↦ ∑ n ∈ range (⌊t⌋₊+ 1), f n

theorem S_at_nat (k : ℕ) :
    S f k = ∑ n ∈ range (k + 1), f n := by simp [S]

theorem integral_repr (s : ℂ) :
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (S f t) / t ^ (s + 1)) := by
  sorry

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ‖S f t - l * t‖ ≤ ε := sorry

theorem step1 (s : ℝ) (ε : ℝ) :
    ∃ c, ‖(LSeries f s) / s - l / (s - 1)‖ ≤ ε / (s - 1) + c := sorry

theorem step2 (ε : ℝ) (hε : 0 < ε) :
    limsup (fun s : ℝ ↦ ‖(s - 1) * LSeries f s - l‖) (𝓝[<] 1) ≤ ε := sorry

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := sorry

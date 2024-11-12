/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Docstring

-/

noncomputable section

open Filter Topology Finset Asymptotics Metric

variable (a : ℕ → ℝ) {l : ℝ}
  (hF : Tendsto (fun n ↦ (∑ k in range (n + 1), a k) / n) atTop (𝓝 1)) (hl : 0 < l)

theorem main (f : ℕ → ℝ → ℝ) (h : ∀ᶠ s in (𝓝[>] 1), (fun n ↦ f n s) ~[atTop] fun n ↦ 1 / n ^ s) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, f n s) (𝓝[>] 1) (𝓝 1) := by
  have : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ s : ℝ,
    (1 - ε) / (n : ℝ) ^ s ≤ f n s ∧ f n s ≤ (1 + ε) / (n : ℝ) ^ s := sorry
  rw [tendsto_nhdsWithin_nhds]
  intro ε hε
  sorry

theorem apply :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, a n / n ^ s) (𝓝[>] 1) (𝓝 1) := by
  let S : ℕ → ℝ := fun n ↦ ∑ k in range (n + 1), a k
  have h₀ : (fun n ↦ S n) ~[atTop] fun n ↦ n := sorry
  have h₁ : ∀ n, 1 ≤ n → a n = S n - S (n - 1) := sorry
  have h₂ : (fun s : ℝ ↦ ∑' n, a n / n ^ s)  =ᶠ[𝓝[>] 1]
    fun s ↦ ∑' n, S n / n ^ s - ∑' n, S (n - 1) / n ^ s := by
    sorry
  have h₃ : (fun s : ℝ ↦ ∑' n, S (n - 1) / n ^ s) =ᶠ[𝓝[>] 1] fun s ↦ ∑' n, S n / (n + 1) ^ s := by
    sorry
  have h₄ : (fun s : ℝ ↦ ∑' n, a n / n ^ s) =ᶠ[𝓝[>] 1]
      fun s ↦ ∑' n, (S n) * (1 / n ^ s - 1 /(n + 1) ^ s) := by
    sorry
  have h₅ : (fun s : ℝ ↦ (s - 1) * ∑' n, a n / n ^ s) =ᶠ[𝓝[>] 1]
      fun s ↦ (s - 1) * ∑' n, (S n) * (1 / n ^ s - 1 /(n + 1) ^ s) := by
    sorry
  refine Tendsto.congr' h₅.symm ?_
  refine main _ ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  


end

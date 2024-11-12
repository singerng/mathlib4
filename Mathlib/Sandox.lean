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

variable (f : ℕ → ℝ) {l : ℝ}
  (hF : Tendsto (fun n ↦ (∑ i in range (n + 1), f i) / n) atTop (𝓝 l)) (hl : 0 < l)

theorem main (f : ℕ → ℝ → ℝ) (l : ℝ) (h : ∀ s, (fun n ↦ f n s) ~[atTop] fun n ↦ 1 / n ^ s) :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' n, f n s) (𝓝[>] 1) (𝓝 1) := by
  
  sorry

end

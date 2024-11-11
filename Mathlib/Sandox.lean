import Mathlib

open NNReal

variable (F : ℕ → ℝ≥0) (hF : ∀ r, {n | F n ≤ r}.Finite)

example : ∃ e : ℕ → ℕ, Monotone (F ∘ e) := sorry



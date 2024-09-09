import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.Finset.Fold

namespace Finset

theorem fold_max_add {α β : Type*} [LinearOrder β] [Add β]
    [CovariantClass β β (Function.swap (· + ·)) (· ≤ ·)] {f : α → β} (n : WithBot β)
    (s : Finset α) : (s.fold max ⊥ fun x : α => ↑(f x) + n) = s.fold max ⊥ ((↑) ∘ f) + n := by
  classical
    induction' s using Finset.induction_on with a s _ ih <;> simp [*, max_add_add_right]

end Finset

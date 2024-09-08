/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Order.Minimal
import Mathlib.Data.Finset.Basic

/-!
# Two lemmas about `Maximal`/`Minimal` for predicates on `Finset`s
-/

namespace Finset

variable {α : Type*} [DecidableEq α] {P : Finset α → Prop} {s : Finset α}

theorem maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [Maximal, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h x hxs hx ↦ hxs <| h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt ↦ by_contra fun hxs ↦ h x hxs (hP ht (insert_subset hxt hst))⟩

theorem minimal_iff_forall_diff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s.erase x) where
  mp h := ⟨h.prop, fun x hxs hx ↦ by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs ↦ by_contra fun hxt ↦
    h.2 x hxs <| hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

end Finset

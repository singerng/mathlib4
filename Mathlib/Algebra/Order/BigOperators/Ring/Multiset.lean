/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

variable {R : Type*} [CanonicallyOrderedCommSemiring R] [Nontrivial R] {m : Multiset R}

@[simp]
lemma CanonicallyOrderedCommSemiring.multiset_prod_pos :
    0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedCommSemiring.list_prod_pos


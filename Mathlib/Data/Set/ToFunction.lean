/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique

/-!
# Set to function

This file provides API for sets that define functions.

## Main definitions
- `Set.asPartialFun` converts `Set (α × α)` to `α → Option α`.
- `Set.asFun` converts `Set (α × α)` to `α → α` if possible.

-/

variable {α : Type*}

namespace Set

section set_as_partial_function

/-- A set `s : Set (α × α)` represents a partial function when for every `x : α` there's at most
one `y : α` with `(x, y) ∈ s`. -/
def isPartialFun (X : Set (α × α)) : Prop :=
  ∀ x : α, {y : α | (x, y) ∈ X}.Subsingleton

open Classical in
/-- Use given set on `α × α` as a partial function. -/
noncomputable def asPartialFun (X : Set (α × α)) : α → Option α :=
  fun a : α => if hb : ∃ b, (a, b) ∈ X then hb.choose else none

theorem asPartialFun_eq {X : Set (α × α)} (hX : isPartialFun X) {a b : α} (hab : (a, b) ∈ X) :
    asPartialFun X a = b := by
  have hba : ∃ b, (a, b) ∈ X := ⟨b, hab⟩
  simpa [asPartialFun, hba] using hX _ _ _ ⟨hba.choose_spec, hab⟩

end set_as_partial_function

section set_as_total_function

/-- Does given set on `α × α` represent a total function? -/
def isFun (X : Set (α × α)) : Prop :=
  ∀ x : α, ∃! y : α, (x, y) ∈ X

theorem isFun.isPartialFun {X : Set (α × α)} (hX : isFun X) : isPartialFun X := by
  intro x y z ⟨hxy, hxz⟩
  have hy := (hX x).choose_spec.2 y hxy
  have hz := (hX x).choose_spec.2 z hxz
  exact hy.trans hz.symm

/-- Turns `s : Set (α × α)` into a total function. Each `x : α` is mapped to the unique `y : α` with
`(x, y) ∈ s`, or to `none` if none exists. -/
noncomputable def asFun {X : Set (α × α)} (hX : isFun X) : α → α :=
  fun a : α => (hX a).choose

theorem asFun_eq {X : Set (α × α)} (hX : isFun X) {a b : α} (hab : (a, b) ∈ X) :
    asFun hX a = b :=
  ((hX a).choose_spec.2 b hab).symm

end set_as_total_function

end Set

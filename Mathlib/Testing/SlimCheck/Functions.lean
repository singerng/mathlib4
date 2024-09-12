/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.List.Sigma
import Mathlib.Data.Int.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Testing.SlimCheck.Sampleable
import Mathlib.Testing.SlimCheck.Testable

/-!
## `slim_check`: generators for functions

This file defines `Sampleable` instances for `α → β` functions and
`ℤ → ℤ` injective functions.

Functions are generated by creating a list of pairs and one more value
using the list as a lookup table and resorting to the additional value
when a value is not found in the table.

Injective functions are generated by creating a list of numbers and
a permutation of that list. The permutation insures that every input
is mapped to a unique output. When an input is not found in the list
the input itself is used as an output.

Injective functions `f : α → α` could be generated easily instead of
`ℤ → ℤ` by generating a `List α`, removing duplicates and creating a
permutation. One has to be careful when generating the domain to make
it vast enough that, when generating arguments to apply `f` to,
they argument should be likely to lie in the domain of `f`. This is
the reason that injective functions `f : ℤ → ℤ` are generated by
fixing the domain to the range `[-2*size .. 2*size]`, with `size`
the size parameter of the `gen` monad.

Much of the machinery provided in this file is applicable to generate
injective functions of type `α → α` and new instances should be easy
to define.

Other classes of functions such as monotone functions can generated using
similar techniques. For monotone functions, generating two lists, sorting them
and matching them should suffice, with appropriate default values.
Some care must be taken for shrinking such functions to make sure
their defining property is invariant through shrinking. Injective
functions are an example of how complicated it can get.
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Sort w}

namespace SlimCheck

/-- Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`withDefault f y` encodes `x ↦ f x` when `x ∈ f` and `x ↦ y`
otherwise.

We use `Σ` to encode mappings instead of `×` because we
rely on the association list API defined in `Mathlib/Data/List/Sigma.lean`.
 -/
inductive TotalFunction (α : Type u) (β : Type v) : Type max u v
  | withDefault : List (Σ _ : α, β) → β → TotalFunction α β

instance TotalFunction.inhabited [Inhabited β] : Inhabited (TotalFunction α β) :=
  ⟨TotalFunction.withDefault ∅ default⟩

namespace TotalFunction

-- Porting note: new
/-- Compose a total function with a regular function on the left -/
def comp {γ : Type w} (f : β → γ) : TotalFunction α β → TotalFunction α γ
  | TotalFunction.withDefault m y => TotalFunction.withDefault
    (m.map <| Sigma.map id fun _ => f) (f y)

/-- Apply a total function to an argument. -/
def apply [DecidableEq α] : TotalFunction α β → α → β
  | TotalFunction.withDefault m y, x => (m.dlookup x).getD y

/-- Implementation of `Repr (TotalFunction α β)`.

Creates a string for a given `Finmap` and output, `x₀ ↦ y₀, .. xₙ ↦ yₙ`
for each of the entries. The brackets are provided by the calling function.
-/
def reprAux [Repr α] [Repr β] (m : List (Σ _ : α, β)) : String :=
  String.join <|
    -- Porting note: No `List.qsort`, so convert back and forth to an `Array`.
    Array.toList <| Array.qsort (lt := fun x y => x < y)
      (m.map fun x => s!"{(repr <| Sigma.fst x)} ↦ {repr <| Sigma.snd x}, ").toArray

/-- Produce a string for a given `TotalFunction`.
The output is of the form `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, _ ↦ y]`.
-/
protected def repr [Repr α] [Repr β] : TotalFunction α β → String
  | TotalFunction.withDefault m y => s!"[{(reprAux m)}_ ↦ {repr y}]"

instance (α : Type u) (β : Type v) [Repr α] [Repr β] : Repr (TotalFunction α β) where
  reprPrec f _ := TotalFunction.repr f

/-- Create a `Finmap` from a list of pairs. -/
def List.toFinmap' (xs : List (α × β)) : List (Σ _ : α, β) :=
  xs.map Prod.toSigma

section

universe ua ub
variable [SampleableExt.{_,u} α] [SampleableExt.{_,ub} β]

-- Porting note: removed, there is no `SizeOf.sizeOf` in the new `Sampleable`

-- /-- Redefine `SizeOf.sizeOf` to follow the structure of `sampleable` instances. -/
-- def Total.sizeof : TotalFunction α β → ℕ
--   | ⟨m, x⟩ => 1 + @SizeOf.sizeOf _ Sampleable.wf m + SizeOf.sizeOf x

-- instance (priority := 2000) : SizeOf (TotalFunction α β) :=
--   ⟨Total.sizeof⟩

variable [DecidableEq α]

/-- Shrink a total function by shrinking the lists that represent it. -/
def shrink {α β} [DecidableEq α] [Shrinkable α] [Shrinkable β] :
    TotalFunction α β → List (TotalFunction α β)
  | ⟨m, x⟩ => (Shrinkable.shrink (m, x)).map fun ⟨m', x'⟩ => ⟨List.dedupKeys m', x'⟩

variable [Repr α]

instance Pi.sampleableExt : SampleableExt (α → β) where
  proxy := TotalFunction α (SampleableExt.proxy β)
  interp f := SampleableExt.interp ∘ f.apply
  sample := do
    let xs : List (_ × _) ← (SampleableExt.sample (α := List (α × β)))
    let ⟨x⟩ ← ULiftable.up.{max u ub} <| (SampleableExt.sample : Gen (SampleableExt.proxy β))
    pure <| TotalFunction.withDefault (List.toFinmap' <| xs.map <|
      Prod.map SampleableExt.interp id) x
  -- note: no way of shrinking the domain without an inverse to `interp`
  shrink := { shrink := letI : Shrinkable α := {}; TotalFunction.shrink }

end

section Finsupp

variable [Zero β]

/-- Map a total_function to one whose default value is zero so that it represents a finsupp. -/
@[simp]
def zeroDefault : TotalFunction α β → TotalFunction α β
  | withDefault A _ => withDefault A 0

variable [DecidableEq α] [DecidableEq β]

/-- The support of a zero default `TotalFunction`. -/
@[simp]
def zeroDefaultSupp : TotalFunction α β → Finset α
  | withDefault A _ =>
    List.toFinset <| (A.dedupKeys.filter fun ab => Sigma.snd ab ≠ 0).map Sigma.fst

/-- Create a finitely supported function from a total function by taking the default value to
zero. -/
def applyFinsupp (tf : TotalFunction α β) : α →₀ β where
  support := zeroDefaultSupp tf
  toFun := tf.zeroDefault.apply
  mem_support_toFun := by
    intro a
    rcases tf with ⟨A, y⟩
    simp only [apply, zeroDefaultSupp, List.mem_map, List.mem_filter, exists_and_right,
      List.mem_toFinset, exists_eq_right, Sigma.exists, Ne, zeroDefault]
    constructor
    · rintro ⟨od, hval, hod⟩
      have := List.mem_dlookup (List.nodupKeys_dedupKeys A) hval
      rw [(_ : List.dlookup a A = od)]
      · simpa using hod
      · simpa [List.dlookup_dedupKeys]
    · intro h
      use (A.dlookup a).getD (0 : β)
      rw [← List.dlookup_dedupKeys] at h ⊢
      simp only [h, ← List.mem_dlookup_iff A.nodupKeys_dedupKeys, and_true_iff, not_false_iff,
        Option.mem_def]
      cases haA : List.dlookup a A.dedupKeys
      · simp [haA] at h
      · simp

variable [SampleableExt α] [SampleableExt β] [Repr α]

instance Finsupp.sampleableExt : SampleableExt (α →₀ β) where
  proxy := TotalFunction α (SampleableExt.proxy β)
  interp := fun f => (f.comp SampleableExt.interp).applyFinsupp
  sample := SampleableExt.sample (α := α → β)
  -- note: no way of shrinking the domain without an inverse to `interp`
  shrink := { shrink := letI : Shrinkable α := {}; TotalFunction.shrink }

-- TODO: support a non-constant codomain type
instance DFinsupp.sampleableExt : SampleableExt (Π₀ _ : α, β) where
  proxy := TotalFunction α (SampleableExt.proxy β)
  interp := fun f => (f.comp SampleableExt.interp).applyFinsupp.toDFinsupp
  sample := SampleableExt.sample (α := α → β)
  -- note: no way of shrinking the domain without an inverse to `interp`
  shrink := { shrink := letI : Shrinkable α := {}; TotalFunction.shrink }

end Finsupp

section SampleableExt

open SampleableExt

instance (priority := 2000) PiPred.sampleableExt [SampleableExt (α → Bool)] :
    SampleableExt.{u + 1} (α → Prop) where
  proxy := proxy (α → Bool)
  interp m x := interp m x
  sample := sample
  shrink := SampleableExt.shrink

instance (priority := 2000) PiUncurry.sampleableExt [SampleableExt (α × β → γ)] :
    SampleableExt.{imax (u + 1) (v + 1) w} (α → β → γ) where
  proxy := proxy (α × β → γ)
  interp m x y := interp m (x, y)
  sample := sample
  shrink := SampleableExt.shrink

end SampleableExt

end TotalFunction

end SlimCheck

-- We need List perm notation from `List` namespace but can't open `_root_.List` directly,
-- so have to close the `SlimCheck` namespace first.
-- Lean issue: https://github.com/leanprover/lean4/issues/3045
open List

namespace SlimCheck

/-- Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`mapToSelf f` encodes `x ↦ f x` when `x ∈ f` and `x ↦ x`,
i.e. `x` to itself, otherwise.

We use `Σ` to encode mappings instead of `×` because we
rely on the association list API defined in `Mathlib/Data/List/Sigma.lean`.
-/
inductive InjectiveFunction (α : Type u) : Type u
  | mapToSelf (xs : List (Σ _ : α, α)) :
      xs.map Sigma.fst ~ xs.map Sigma.snd → List.Nodup (xs.map Sigma.snd) → InjectiveFunction α

instance : Inhabited (InjectiveFunction α) :=
  ⟨⟨[], List.Perm.nil, List.nodup_nil⟩⟩

namespace InjectiveFunction

/-- Apply a total function to an argument. -/
def apply [DecidableEq α] : InjectiveFunction α → α → α
  | InjectiveFunction.mapToSelf m _ _, x => (m.dlookup x).getD x

/-- Produce a string for a given `InjectiveFunction`.
The output is of the form `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, x ↦ x]`.
Unlike for `TotalFunction`, the default value is not a constant
but the identity function.
-/
protected def repr [Repr α] : InjectiveFunction α → String
  | InjectiveFunction.mapToSelf m _ _ => s! "[{TotalFunction.reprAux m}x ↦ x]"

instance (α : Type u) [Repr α] : Repr (InjectiveFunction α) where
  reprPrec f _p := InjectiveFunction.repr f

/-- Interpret a list of pairs as a total function, defaulting to
the identity function when no entries are found for a given function -/
def List.applyId [DecidableEq α] (xs : List (α × α)) (x : α) : α :=
  ((xs.map Prod.toSigma).dlookup x).getD x

@[simp]
theorem List.applyId_cons [DecidableEq α] (xs : List (α × α)) (x y z : α) :
    List.applyId ((y, z)::xs) x = if y = x then z else List.applyId xs x := by
  simp only [List.applyId, List.dlookup, eq_rec_constant, Prod.toSigma, List.map]
  split_ifs <;> rfl

open Function
open List

open Nat

theorem List.applyId_zip_eq [DecidableEq α] {xs ys : List α} (h₀ : List.Nodup xs)
    (h₁ : xs.length = ys.length) (x y : α) (i : ℕ) (h₂ : xs[i]? = some x) :
    List.applyId.{u} (xs.zip ys) x = y ↔ ys[i]? = some y := by
  induction xs generalizing ys i with
  | nil => cases h₂
  | cons x' xs xs_ih =>
    cases i
    · simp only [length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        getElem?_eq_getElem, getElem_cons_zero, Option.some.injEq] at h₂
      subst h₂
      cases ys
      · cases h₁
      · simp only [applyId, map, Prod.toSigma, dlookup_cons_eq, Option.getD_some,
          getElem?_cons_zero, Option.some.injEq]
    · cases ys
      · cases h₁
      · cases' h₀ with _ _ h₀ h₁
        simp only [getElem?_cons_succ, zip_cons_cons, applyId_cons] at h₂ ⊢
        rw [if_neg]
        · apply xs_ih <;> solve_by_elim [Nat.succ.inj]
        · apply h₀; apply List.getElem?_mem h₂

theorem applyId_mem_iff [DecidableEq α] {xs ys : List α} (h₀ : List.Nodup xs) (h₁ : xs ~ ys)
    (x : α) : List.applyId.{u} (xs.zip ys) x ∈ ys ↔ x ∈ xs := by
  simp only [List.applyId]
  cases h₃ : List.dlookup x (List.map Prod.toSigma (xs.zip ys)) with
  | none =>
    dsimp [Option.getD]
    rw [h₁.mem_iff]
  | some val =>
    have h₂ : ys.Nodup := h₁.nodup_iff.1 h₀
    replace h₁ : xs.length = ys.length := h₁.length_eq
    dsimp
    induction xs generalizing ys with
    | nil => contradiction
    | cons x' xs xs_ih =>
      cases' ys with y ys
      · cases h₃
      dsimp [List.dlookup] at h₃; split_ifs at h₃ with h
      · rw [Option.some_inj] at h₃
        subst x'; subst val
        simp only [List.mem_cons, true_or_iff, eq_self_iff_true]
      · cases' h₀ with _ _ h₀ h₅
        cases' h₂ with _ _ h₂ h₄
        have h₆ := Nat.succ.inj h₁
        specialize xs_ih h₅ h₃ h₄ h₆
        simp only [Ne.symm h, xs_ih, List.mem_cons, false_or_iff]
        suffices val ∈ ys by tauto
        erw [← Option.mem_def, List.mem_dlookup_iff] at h₃
        · simp only [Prod.toSigma, List.mem_map, heq_iff_eq, Prod.exists] at h₃
          rcases h₃ with ⟨a, b, h₃, h₄, h₅⟩
          apply (List.of_mem_zip h₃).2
        simp only [List.NodupKeys, List.keys, comp_def, Prod.fst_toSigma, List.map_map]
        rwa [List.map_fst_zip _ _ (le_of_eq h₆)]

theorem List.applyId_eq_self [DecidableEq α] {xs ys : List α} (x : α) :
    x ∉ xs → List.applyId.{u} (xs.zip ys) x = x := by
  intro h
  dsimp [List.applyId]
  rw [List.dlookup_eq_none.2]
  · rfl
  simp only [List.keys, not_exists, Prod.toSigma, exists_and_right, exists_eq_right, List.mem_map,
    Function.comp_apply, List.map_map, Prod.exists]
  intro y hy
  exact h (List.of_mem_zip hy).1

theorem applyId_injective [DecidableEq α] {xs ys : List α} (h₀ : List.Nodup xs) (h₁ : xs ~ ys) :
    Injective.{u + 1, u + 1} (List.applyId (xs.zip ys)) := by
  intro x y h
  by_cases hx : x ∈ xs <;> by_cases hy : y ∈ xs
  · rw [List.mem_iff_getElem?] at hx hy
    cases' hx with i hx
    cases' hy with j hy
    suffices some x = some y by injection this
    have h₂ := h₁.length_eq
    rw [List.applyId_zip_eq h₀ h₂ _ _ _ hx] at h
    rw [← hx, ← hy]; congr
    apply List.getElem?_inj _ (h₁.nodup_iff.1 h₀)
    · symm; rw [h]
      rw [← List.applyId_zip_eq] <;> assumption
    · rw [← h₁.length_eq]
      rw [List.getElem?_eq_some_iff] at hx
      cases' hx with hx hx'
      exact hx
  · rw [← applyId_mem_iff h₀ h₁] at hx hy
    rw [h] at hx
    contradiction
  · rw [← applyId_mem_iff h₀ h₁] at hx hy
    rw [h] at hx
    contradiction
  · rwa [List.applyId_eq_self, List.applyId_eq_self] at h <;> assumption

open TotalFunction (List.toFinmap')

open SampleableExt

/-- Remove a slice of length `m` at index `n` in a list and a permutation, maintaining the property
that it is a permutation.
-/
def Perm.slice [DecidableEq α] (n m : ℕ) :
    (Σ' xs ys : List α, xs ~ ys ∧ ys.Nodup) → Σ' xs ys : List α, xs ~ ys ∧ ys.Nodup
  | ⟨xs, ys, h, h'⟩ =>
    let xs' := List.dropSlice n m xs
    have h₀ : xs' ~ ys.inter xs' := List.Perm.dropSlice_inter _ _ h h'
    ⟨xs', ys.inter xs', h₀, h'.inter _⟩

/-- A list, in decreasing order, of sizes that should be
sliced off a list of length `n`
-/
def sliceSizes : ℕ → MLList Id ℕ+
  | n =>
    if h : 0 < n then
      have : n / 2 < n := Nat.div_lt_self h (by decide : 1 < 2)
      .cons ⟨_, h⟩ (sliceSizes <| n / 2)
    else .nil

/-- Shrink a permutation of a list, slicing a segment in the middle.

The sizes of the slice being removed start at `n` (with `n` the length
of the list) and then `n / 2`, then `n / 4`, etc down to 1. The slices
will be taken at index `0`, `n / k`, `2n / k`, `3n / k`, etc.
-/
protected def shrinkPerm {α : Type} [DecidableEq α] :
    (Σ' xs ys : List α, xs ~ ys ∧ ys.Nodup) → List (Σ' xs ys : List α, xs ~ ys ∧ ys.Nodup)
  | xs => do
    let k := xs.1.length
    let n ← (sliceSizes k).force
    let i ← List.finRange <| k / n
    pure <| Perm.slice (i * n) n xs


-- Porting note: removed, there is no `sizeof` in the new `Sampleable`
-- instance [SizeOf α] : SizeOf (InjectiveFunction α) :=
--   ⟨fun ⟨xs, _, _⟩ => SizeOf.sizeOf (xs.map Sigma.fst)⟩

/-- Shrink an injective function slicing a segment in the middle of the domain and removing
the corresponding elements in the codomain, hence maintaining the property that
one is a permutation of the other.
-/
protected def shrink {α : Type} [DecidableEq α] :
    InjectiveFunction α → List (InjectiveFunction α)
  | ⟨xs, h₀, h₁⟩ => do
    let ⟨xs', ys', h₀, h₁⟩ ← InjectiveFunction.shrinkPerm ⟨_, _, h₀, h₁⟩
    have h₃ : xs'.length ≤ ys'.length := le_of_eq (List.Perm.length_eq h₀)
    have h₄ : ys'.length ≤ xs'.length := le_of_eq (List.Perm.length_eq h₀.symm)
    pure
      ⟨(List.zip xs' ys').map Prod.toSigma,
        by simp only [comp_def, List.map_fst_zip, List.map_snd_zip, *, Prod.fst_toSigma,
          Prod.snd_toSigma, List.map_map],
        by simp only [comp_def, List.map_snd_zip, *, Prod.snd_toSigma, List.map_map]⟩

/-- Create an injective function from one list and a permutation of that list. -/
protected def mk (xs ys : List α) (h : xs ~ ys) (h' : ys.Nodup) : InjectiveFunction α :=
  have h₀ : xs.length ≤ ys.length := le_of_eq h.length_eq
  have h₁ : ys.length ≤ xs.length := le_of_eq h.length_eq.symm
  InjectiveFunction.mapToSelf (List.toFinmap' (xs.zip ys))
    (by
      simp only [List.toFinmap', comp_def, List.map_fst_zip, List.map_snd_zip, *, Prod.fst_toSigma,
        Prod.snd_toSigma, List.map_map])
    (by simp only [List.toFinmap', comp_def, List.map_snd_zip, *, Prod.snd_toSigma, List.map_map])

protected theorem injective [DecidableEq α] (f : InjectiveFunction α) : Injective (apply f) := by
  cases' f with xs hperm hnodup
  generalize h₀ : List.map Sigma.fst xs = xs₀
  generalize h₁ : xs.map (@id ((Σ _ : α, α) → α) <| @Sigma.snd α fun _ : α => α) = xs₁
  dsimp [id] at h₁
  have hxs : xs = TotalFunction.List.toFinmap' (xs₀.zip xs₁) := by
    rw [← h₀, ← h₁, List.toFinmap']; clear h₀ h₁ xs₀ xs₁ hperm hnodup
    induction xs with
    | nil => simp only [List.zip_nil_right, List.map_nil]
    | cons xs_hd xs_tl xs_ih =>
      simp only [true_and_iff, Prod.toSigma, eq_self_iff_true, Sigma.eta, List.zip_cons_cons,
        List.map, List.cons_inj_right]
      exact xs_ih
  revert hperm hnodup
  rw [hxs]; intros hperm hnodup
  apply InjectiveFunction.applyId_injective
  · rwa [← h₀, hxs, hperm.nodup_iff]
  · rwa [← hxs, h₀, h₁] at hperm

instance PiInjective.sampleableExt : SampleableExt { f : ℤ → ℤ // Function.Injective f } where
  proxy := InjectiveFunction ℤ
  interp f := ⟨apply f, f.injective⟩
  sample := do
    let ⟨sz⟩ ← ULiftable.up Gen.getSize
    let xs' := Int.range (-(2 * sz + 2)) (2 * sz + 2)
    let ys ← Gen.permutationOf xs'
    have Hinj : Injective fun r : ℕ => -(2 * sz + 2 : ℤ) + ↑r := fun _x _y h =>
        Int.ofNat.inj (add_right_injective _ h)
    let r : InjectiveFunction ℤ :=
      InjectiveFunction.mk.{0} xs' ys.1 ys.2 (ys.2.nodup_iff.1 <| (List.nodup_range _).map Hinj)
    pure r
  shrink := {shrink := @InjectiveFunction.shrink ℤ _ }

end InjectiveFunction

open Function

instance Injective.testable (f : α → β)
    [I : Testable (NamedBinder "x" <|
      ∀ x : α, NamedBinder "y" <| ∀ y : α, NamedBinder "H" <| f x = f y → x = y)] :
    Testable (Injective f) :=
  I

instance Monotone.testable [Preorder α] [Preorder β] (f : α → β)
    [I : Testable (NamedBinder "x" <|
      ∀ x : α, NamedBinder "y" <| ∀ y : α, NamedBinder "H" <| x ≤ y → f x ≤ f y)] :
    Testable (Monotone f) :=
  I

instance Antitone.testable [Preorder α] [Preorder β] (f : α → β)
    [I : Testable (NamedBinder "x" <|
      ∀ x : α, NamedBinder "y" <| ∀ y : α, NamedBinder "H" <| x ≤ y → f y ≤ f x)] :
    Testable (Antitone f) :=
  I

end SlimCheck

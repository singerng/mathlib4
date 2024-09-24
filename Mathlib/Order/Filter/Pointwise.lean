/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Order.Filter.NAry
import Mathlib.Order.Filter.Ultrafilter

/-!
# Pointwise operations on filters

This file defines pointwise operations on filters. This is useful because usual algebraic operations
distribute over pointwise operations. For example,
* `(f₁ * f₂).map m = f₁.map m * f₂.map m`
* `𝓝 (x * y) = 𝓝 x * 𝓝 y`

## Main declarations

* `0` (`Filter.instZero`): Pure filter at `0 : α`, or alternatively principal filter at `0 : Set α`.
* `1` (`Filter.instOne`): Pure filter at `1 : α`, or alternatively principal filter at `1 : Set α`.
* `f + g` (`Filter.instAdd`): Addition, filter generated by all `s + t` where `s ∈ f` and `t ∈ g`.
* `f * g` (`Filter.instMul`): Multiplication, filter generated by all `s * t` where `s ∈ f` and
  `t ∈ g`.
* `-f` (`Filter.instNeg`): Negation, filter of all `-s` where `s ∈ f`.
* `f⁻¹` (`Filter.instInv`): Inversion, filter of all `s⁻¹` where `s ∈ f`.
* `f - g` (`Filter.instSub`): Subtraction, filter generated by all `s - t` where `s ∈ f` and
  `t ∈ g`.
* `f / g` (`Filter.instDiv`): Division, filter generated by all `s / t` where `s ∈ f` and `t ∈ g`.
* `f +ᵥ g` (`Filter.instVAdd`): Scalar addition, filter generated by all `s +ᵥ t` where `s ∈ f` and
  `t ∈ g`.
* `f -ᵥ g` (`Filter.instVSub`): Scalar subtraction, filter generated by all `s -ᵥ t` where `s ∈ f`
  and `t ∈ g`.
* `f • g` (`Filter.instSMul`): Scalar multiplication, filter generated by all `s • t` where
  `s ∈ f` and `t ∈ g`.
* `a +ᵥ f` (`Filter.instVAddFilter`): Translation, filter of all `a +ᵥ s` where `s ∈ f`.
* `a • f` (`Filter.instSMulFilter`): Scaling, filter of all `a • s` where `s ∈ f`.

For `α` a semigroup/monoid, `Filter α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • f`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition. See note [pointwise nat action].

## Implementation notes

We put all instances in the locale `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

filter multiplication, filter addition, pointwise addition, pointwise multiplication,
-/


open Function Set Filter Pointwise

variable {F α β γ δ ε : Type*}

namespace Filter

/-! ### `0`/`1` as filters -/


section One

variable [One α] {f : Filter α} {s : Set α}

/-- `1 : Filter α` is defined as the filter of sets containing `1 : α` in locale `Pointwise`. -/
@[to_additive
      "`0 : Filter α` is defined as the filter of sets containing `0 : α` in locale `Pointwise`."]
protected def instOne : One (Filter α) :=
  ⟨pure 1⟩

scoped[Pointwise] attribute [instance] Filter.instOne Filter.instZero

@[to_additive (attr := simp)]
theorem mem_one : s ∈ (1 : Filter α) ↔ (1 : α) ∈ s :=
  mem_pure

@[to_additive]
theorem one_mem_one : (1 : Set α) ∈ (1 : Filter α) :=
  mem_pure.2 Set.one_mem_one

@[to_additive (attr := simp)]
theorem pure_one : pure 1 = (1 : Filter α) :=
  rfl

@[to_additive (attr := simp) zero_prod]
theorem one_prod {l : Filter β} : (1 : Filter α) ×ˢ l = map (1, ·) l := pure_prod

@[to_additive (attr := simp) prod_zero]
theorem prod_one {l : Filter β} : l ×ˢ (1 : Filter α) = map (·, 1) l := prod_pure

@[to_additive (attr := simp)]
theorem principal_one : 𝓟 1 = (1 : Filter α) :=
  principal_singleton _

@[to_additive]
theorem one_neBot : (1 : Filter α).NeBot :=
  Filter.pure_neBot

scoped[Pointwise] attribute [instance] one_neBot zero_neBot

@[to_additive (attr := simp)]
protected theorem map_one' (f : α → β) : (1 : Filter α).map f = pure (f 1) :=
  rfl

@[to_additive (attr := simp)]
theorem le_one_iff : f ≤ 1 ↔ (1 : Set α) ∈ f :=
  le_pure_iff

@[to_additive]
protected theorem NeBot.le_one_iff (h : f.NeBot) : f ≤ 1 ↔ f = 1 :=
  h.le_pure_iff

@[to_additive (attr := simp)]
theorem eventually_one {p : α → Prop} : (∀ᶠ x in 1, p x) ↔ p 1 :=
  eventually_pure

@[to_additive (attr := simp)]
theorem tendsto_one {a : Filter β} {f : β → α} : Tendsto f a 1 ↔ ∀ᶠ x in a, f x = 1 :=
  tendsto_pure

@[to_additive zero_prod_zero]
theorem one_prod_one [One β] : (1 : Filter α) ×ˢ (1 : Filter β) = 1 :=
  prod_pure_pure

@[deprecated (since := "2024-08-16")] alias zero_sum_zero := zero_prod_zero

/-- `pure` as a `OneHom`. -/
@[to_additive "`pure` as a `ZeroHom`."]
def pureOneHom : OneHom α (Filter α) where
  toFun := pure; map_one' := pure_one

@[to_additive (attr := simp)]
theorem coe_pureOneHom : (pureOneHom : α → Filter α) = pure :=
  rfl

@[to_additive (attr := simp)]
theorem pureOneHom_apply (a : α) : pureOneHom a = pure a :=
  rfl

variable [One β]

@[to_additive]
-- Porting note (#11119): removed `simp` attribute because `simpNF` says it can prove it.
protected theorem map_one [FunLike F α β] [OneHomClass F α β] (φ : F) : map φ 1 = 1 := by
  rw [Filter.map_one', map_one, pure_one]

end One

/-! ### Filter negation/inversion -/


section Inv

variable [Inv α] {f g : Filter α} {s : Set α} {a : α}

/-- The inverse of a filter is the pointwise preimage under `⁻¹` of its sets. -/
@[to_additive "The negation of a filter is the pointwise preimage under `-` of its sets."]
instance instInv : Inv (Filter α) :=
  ⟨map Inv.inv⟩

@[to_additive (attr := simp)]
protected theorem map_inv : f.map Inv.inv = f⁻¹ :=
  rfl

@[to_additive]
theorem mem_inv : s ∈ f⁻¹ ↔ Inv.inv ⁻¹' s ∈ f :=
  Iff.rfl

@[to_additive]
protected theorem inv_le_inv (hf : f ≤ g) : f⁻¹ ≤ g⁻¹ :=
  map_mono hf

@[to_additive (attr := simp)]
theorem inv_pure : (pure a : Filter α)⁻¹ = pure a⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_eq_bot_iff : f⁻¹ = ⊥ ↔ f = ⊥ :=
  map_eq_bot_iff

@[to_additive (attr := simp)]
theorem neBot_inv_iff : f⁻¹.NeBot ↔ NeBot f :=
  map_neBot_iff _

@[to_additive]
protected theorem NeBot.inv : f.NeBot → f⁻¹.NeBot := fun h => h.map _

@[to_additive neg.instNeBot]
lemma inv.instNeBot [NeBot f] : NeBot f⁻¹ := .inv ‹_›

scoped[Pointwise] attribute [instance] inv.instNeBot neg.instNeBot

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {f g : Filter α} {s : Set α}

@[to_additive (attr := simp)]
protected lemma comap_inv : comap Inv.inv f = f⁻¹ :=
  .symm <| map_eq_comap_of_inverse (inv_comp_inv _) (inv_comp_inv _)

@[to_additive]
theorem inv_mem_inv (hs : s ∈ f) : s⁻¹ ∈ f⁻¹ := by rwa [mem_inv, inv_preimage, inv_inv]

/-- Inversion is involutive on `Filter α` if it is on `α`. -/
@[to_additive "Negation is involutive on `Filter α` if it is on `α`."]
protected def instInvolutiveInv : InvolutiveInv (Filter α) :=
  { Filter.instInv with
    inv_inv := fun f => map_map.trans <| by rw [inv_involutive.comp_self, map_id] }

scoped[Pointwise] attribute [instance] Filter.instInvolutiveInv Filter.instInvolutiveNeg

@[to_additive (attr := simp)]
protected theorem inv_le_inv_iff : f⁻¹ ≤ g⁻¹ ↔ f ≤ g :=
  ⟨fun h => inv_inv f ▸ inv_inv g ▸ Filter.inv_le_inv h, Filter.inv_le_inv⟩

@[to_additive]
theorem inv_le_iff_le_inv : f⁻¹ ≤ g ↔ f ≤ g⁻¹ := by rw [← Filter.inv_le_inv_iff, inv_inv]

@[to_additive (attr := simp)]
theorem inv_le_self : f⁻¹ ≤ f ↔ f⁻¹ = f :=
  ⟨fun h => h.antisymm <| inv_le_iff_le_inv.1 h, Eq.le⟩

end InvolutiveInv

@[to_additive (attr := simp)]
lemma inv_atTop {G : Type*} [OrderedCommGroup G] : (atTop : Filter G)⁻¹ = atBot :=
  (OrderIso.inv G).map_atTop

/-! ### Filter addition/multiplication -/

section Mul

variable [Mul α] [Mul β] {f f₁ f₂ g g₁ g₂ h : Filter α} {s t : Set α} {a b : α}

/-- The filter `f * g` is generated by `{s * t | s ∈ f, t ∈ g}` in locale `Pointwise`. -/
@[to_additive "The filter `f + g` is generated by `{s + t | s ∈ f, t ∈ g}` in locale `Pointwise`."]
protected def instMul : Mul (Filter α) :=
  ⟨/- This is defeq to `map₂ (· * ·) f g`, but the hypothesis unfolds to `t₁ * t₂ ⊆ s` rather
  than all the way to `Set.image2 (· * ·) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· * ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ * t₂ ⊆ s } }⟩

scoped[Pointwise] attribute [instance] Filter.instMul Filter.instAdd

@[to_additive (attr := simp)]
theorem map₂_mul : map₂ (· * ·) f g = f * g :=
  rfl

@[to_additive]
theorem mem_mul : s ∈ f * g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ * t₂ ⊆ s :=
  Iff.rfl

@[to_additive]
theorem mul_mem_mul : s ∈ f → t ∈ g → s * t ∈ f * g :=
  image2_mem_map₂

@[to_additive (attr := simp)]
theorem bot_mul : ⊥ * g = ⊥ :=
  map₂_bot_left

@[to_additive (attr := simp)]
theorem mul_bot : f * ⊥ = ⊥ :=
  map₂_bot_right

@[to_additive (attr := simp)]
theorem mul_eq_bot_iff : f * g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
  map₂_eq_bot_iff

@[to_additive (attr := simp)] -- TODO: make this a scoped instance in the `Pointwise` namespace
lemma mul_neBot_iff : (f * g).NeBot ↔ f.NeBot ∧ g.NeBot :=
  map₂_neBot_iff

@[to_additive]
protected theorem NeBot.mul : NeBot f → NeBot g → NeBot (f * g) :=
  NeBot.map₂

@[to_additive]
theorem NeBot.of_mul_left : (f * g).NeBot → f.NeBot :=
  NeBot.of_map₂_left

@[to_additive]
theorem NeBot.of_mul_right : (f * g).NeBot → g.NeBot :=
  NeBot.of_map₂_right

@[to_additive add.instNeBot]
protected lemma mul.instNeBot [NeBot f] [NeBot g] : NeBot (f * g) := .mul ‹_› ‹_›

scoped[Pointwise] attribute [instance] mul.instNeBot add.instNeBot

@[to_additive (attr := simp)]
theorem pure_mul : pure a * g = g.map (a * ·) :=
  map₂_pure_left

@[to_additive (attr := simp)]
theorem mul_pure : f * pure b = f.map (· * b) :=
  map₂_pure_right

@[to_additive]
-- Porting note (#11119): removed `simp` attribute because `simpNF` says it can prove it.
theorem pure_mul_pure : (pure a : Filter α) * pure b = pure (a * b) :=
  map₂_pure

@[to_additive (attr := simp)]
theorem le_mul_iff : h ≤ f * g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s * t ∈ h :=
  le_map₂_iff

@[to_additive]
instance covariant_mul : CovariantClass (Filter α) (Filter α) (· * ·) (· ≤ ·) :=
  ⟨fun _ _ _ => map₂_mono_left⟩

@[to_additive]
instance covariant_swap_mul : CovariantClass (Filter α) (Filter α) (swap (· * ·)) (· ≤ ·) :=
  ⟨fun _ _ _ => map₂_mono_right⟩

@[to_additive]
protected theorem map_mul [FunLike F α β] [MulHomClass F α β] (m : F) :
    (f₁ * f₂).map m = f₁.map m * f₂.map m :=
  map_map₂_distrib <| map_mul m

/-- `pure` operation as a `MulHom`. -/
@[to_additive "The singleton operation as an `AddHom`."]
def pureMulHom : α →ₙ* Filter α where
  toFun := pure; map_mul' _ _ := pure_mul_pure.symm

@[to_additive (attr := simp)]
theorem coe_pureMulHom : (pureMulHom : α → Filter α) = pure :=
  rfl

@[to_additive (attr := simp)]
theorem pureMulHom_apply (a : α) : pureMulHom a = pure a :=
  rfl

end Mul

/-! ### Filter subtraction/division -/

section Div

variable [Div α] {f f₁ f₂ g g₁ g₂ h : Filter α} {s t : Set α} {a b : α}

/-- The filter `f / g` is generated by `{s / t | s ∈ f, t ∈ g}` in locale `Pointwise`. -/
@[to_additive "The filter `f - g` is generated by `{s - t | s ∈ f, t ∈ g}` in locale `Pointwise`."]
protected def instDiv : Div (Filter α) :=
  ⟨/- This is defeq to `map₂ (· / ·) f g`, but the hypothesis unfolds to `t₁ / t₂ ⊆ s`
  rather than all the way to `Set.image2 (· / ·) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· / ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ / t₂ ⊆ s } }⟩

scoped[Pointwise] attribute [instance] Filter.instDiv Filter.instSub

@[to_additive (attr := simp)]
theorem map₂_div : map₂ (· / ·) f g = f / g :=
  rfl

@[to_additive]
theorem mem_div : s ∈ f / g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ / t₂ ⊆ s :=
  Iff.rfl

@[to_additive]
theorem div_mem_div : s ∈ f → t ∈ g → s / t ∈ f / g :=
  image2_mem_map₂

@[to_additive (attr := simp)]
theorem bot_div : ⊥ / g = ⊥ :=
  map₂_bot_left

@[to_additive (attr := simp)]
theorem div_bot : f / ⊥ = ⊥ :=
  map₂_bot_right

@[to_additive (attr := simp)]
theorem div_eq_bot_iff : f / g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
  map₂_eq_bot_iff

@[to_additive (attr := simp)]
theorem div_neBot_iff : (f / g).NeBot ↔ f.NeBot ∧ g.NeBot :=
  map₂_neBot_iff

@[to_additive]
protected theorem NeBot.div : NeBot f → NeBot g → NeBot (f / g) :=
  NeBot.map₂

@[to_additive]
theorem NeBot.of_div_left : (f / g).NeBot → f.NeBot :=
  NeBot.of_map₂_left

@[to_additive]
theorem NeBot.of_div_right : (f / g).NeBot → g.NeBot :=
  NeBot.of_map₂_right

@[to_additive sub.instNeBot]
lemma div.instNeBot [NeBot f] [NeBot g] : NeBot (f / g) := .div ‹_› ‹_›

scoped[Pointwise] attribute [instance] div.instNeBot sub.instNeBot

@[to_additive (attr := simp)]
theorem pure_div : pure a / g = g.map (a / ·) :=
  map₂_pure_left

@[to_additive (attr := simp)]
theorem div_pure : f / pure b = f.map (· / b) :=
  map₂_pure_right

@[to_additive]
-- Porting note (#11119): removed `simp` attribute because `simpNF` says it can prove it.
theorem pure_div_pure : (pure a : Filter α) / pure b = pure (a / b) :=
  map₂_pure

@[to_additive]
protected theorem div_le_div : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ / g₁ ≤ f₂ / g₂ :=
  map₂_mono

@[to_additive]
protected theorem div_le_div_left : g₁ ≤ g₂ → f / g₁ ≤ f / g₂ :=
  map₂_mono_left

@[to_additive]
protected theorem div_le_div_right : f₁ ≤ f₂ → f₁ / g ≤ f₂ / g :=
  map₂_mono_right

@[to_additive (attr := simp)]
protected theorem le_div_iff : h ≤ f / g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s / t ∈ h :=
  le_map₂_iff

@[to_additive]
instance covariant_div : CovariantClass (Filter α) (Filter α) (· / ·) (· ≤ ·) :=
  ⟨fun _ _ _ => map₂_mono_left⟩

@[to_additive]
instance covariant_swap_div : CovariantClass (Filter α) (Filter α) (swap (· / ·)) (· ≤ ·) :=
  ⟨fun _ _ _ => map₂_mono_right⟩

end Div

open Pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Filter`. See
Note [pointwise nat action]. -/
protected def instNSMul [Zero α] [Add α] : SMul ℕ (Filter α) :=
  ⟨nsmulRec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Filter`. See Note [pointwise nat action]. -/
@[to_additive existing]
protected def instNPow [One α] [Mul α] : Pow (Filter α) ℕ :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Filter`. See Note [pointwise nat action]. -/
protected def instZSMul [Zero α] [Add α] [Neg α] : SMul ℤ (Filter α) :=
  ⟨zsmulRec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Filter`. See Note [pointwise nat action]. -/
@[to_additive existing]
protected def instZPow [One α] [Mul α] [Inv α] : Pow (Filter α) ℤ :=
  ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Filter.instNSMul Filter.instNPow
  Filter.instZSMul Filter.instZPow

/-- `Filter α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive "`Filter α` is an `AddSemigroup` under pointwise operations if `α` is."]
protected def semigroup [Semigroup α] : Semigroup (Filter α) where
  mul := (· * ·)
  mul_assoc _ _ _ := map₂_assoc mul_assoc

/-- `Filter α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive "`Filter α` is an `AddCommSemigroup` under pointwise operations if `α` is."]
protected def commSemigroup [CommSemigroup α] : CommSemigroup (Filter α) :=
  { Filter.semigroup with mul_comm := fun _ _ => map₂_comm mul_comm }

section MulOneClass

variable [MulOneClass α] [MulOneClass β]

/-- `Filter α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive "`Filter α` is an `AddZeroClass` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Filter α) where
  one := 1
  mul := (· * ·)
  one_mul := map₂_left_identity one_mul
  mul_one := map₂_right_identity mul_one

scoped[Pointwise] attribute [instance] Filter.semigroup Filter.addSemigroup
  Filter.commSemigroup Filter.addCommSemigroup Filter.mulOneClass Filter.addZeroClass

variable [FunLike F α β]

/-- If `φ : α →* β` then `mapMonoidHom φ` is the monoid homomorphism
`Filter α →* Filter β` induced by `map φ`. -/
@[to_additive "If `φ : α →+ β` then `mapAddMonoidHom φ` is the monoid homomorphism
 `Filter α →+ Filter β` induced by `map φ`."]
def mapMonoidHom [MonoidHomClass F α β] (φ : F) : Filter α →* Filter β where
  toFun := map φ
  map_one' := Filter.map_one φ
  map_mul' _ _ := Filter.map_mul φ

-- The other direction does not hold in general
@[to_additive]
theorem comap_mul_comap_le [MulHomClass F α β] (m : F) {f g : Filter β} :
    f.comap m * g.comap m ≤ (f * g).comap m := fun _ ⟨_, ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩, mt⟩ =>
  ⟨m ⁻¹' t₁, ⟨t₁, ht₁, Subset.rfl⟩, m ⁻¹' t₂, ⟨t₂, ht₂, Subset.rfl⟩,
    (preimage_mul_preimage_subset _).trans <| (preimage_mono t₁t₂).trans mt⟩

@[to_additive]
theorem Tendsto.mul_mul [MulHomClass F α β] (m : F) {f₁ g₁ : Filter α} {f₂ g₂ : Filter β} :
    Tendsto m f₁ f₂ → Tendsto m g₁ g₂ → Tendsto m (f₁ * g₁) (f₂ * g₂) := fun hf hg =>
  (Filter.map_mul m).trans_le <| mul_le_mul' hf hg

/-- `pure` as a `MonoidHom`. -/
@[to_additive "`pure` as an `AddMonoidHom`."]
def pureMonoidHom : α →* Filter α :=
  { pureMulHom, pureOneHom with }

@[to_additive (attr := simp)]
theorem coe_pureMonoidHom : (pureMonoidHom : α → Filter α) = pure :=
  rfl

@[to_additive (attr := simp)]
theorem pureMonoidHom_apply (a : α) : pureMonoidHom a = pure a :=
  rfl

end MulOneClass

section Monoid

variable [Monoid α] {f g : Filter α} {s : Set α} {a : α} {m n : ℕ}

/-- `Filter α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive "`Filter α` is an `AddMonoid` under pointwise operations if `α` is."]
protected def monoid : Monoid (Filter α) :=
  { Filter.mulOneClass, Filter.semigroup, @Filter.instNPow α _ _ with }

scoped[Pointwise] attribute [instance] Filter.monoid Filter.addMonoid

@[to_additive]
theorem pow_mem_pow (hs : s ∈ f) : ∀ n : ℕ, s ^ n ∈ f ^ n
  | 0 => by
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_mul (pow_mem_pow hs n) hs

@[to_additive (attr := simp) nsmul_bot]
theorem bot_pow {n : ℕ} (hn : n ≠ 0) : (⊥ : Filter α) ^ n = ⊥ := by
  rw [← Nat.sub_one_add_one hn, pow_succ', bot_mul]

@[to_additive]
theorem mul_top_of_one_le (hf : 1 ≤ f) : f * ⊤ = ⊤ := by
  refine top_le_iff.1 fun s => ?_
  simp only [mem_mul, mem_top, exists_and_left, exists_eq_left]
  rintro ⟨t, ht, hs⟩
  rwa [mul_univ_of_one_mem (mem_one.1 <| hf ht), univ_subset_iff] at hs

@[to_additive]
theorem top_mul_of_one_le (hf : 1 ≤ f) : ⊤ * f = ⊤ := by
  refine top_le_iff.1 fun s => ?_
  simp only [mem_mul, mem_top, exists_and_left, exists_eq_left]
  rintro ⟨t, ht, hs⟩
  rwa [univ_mul_of_one_mem (mem_one.1 <| hf ht), univ_subset_iff] at hs

@[to_additive (attr := simp)]
theorem top_mul_top : (⊤ : Filter α) * ⊤ = ⊤ :=
  mul_top_of_one_le le_top

@[to_additive nsmul_top]
theorem top_pow : ∀ {n : ℕ}, n ≠ 0 → (⊤ : Filter α) ^ n = ⊤
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, top_pow n.succ_ne_zero, top_mul_top]

@[to_additive]
protected theorem _root_.IsUnit.filter : IsUnit a → IsUnit (pure a : Filter α) :=
  IsUnit.map (pureMonoidHom : α →* Filter α)

end Monoid

/-- `Filter α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive "`Filter α` is an `AddCommMonoid` under pointwise operations if `α` is."]
protected def commMonoid [CommMonoid α] : CommMonoid (Filter α) :=
  { Filter.mulOneClass, Filter.commSemigroup with }

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {f g : Filter α}

@[to_additive]
protected theorem mul_eq_one_iff : f * g = 1 ↔ ∃ a b, f = pure a ∧ g = pure b ∧ a * b = 1 := by
  refine ⟨fun hfg => ?_, ?_⟩
  · obtain ⟨t₁, h₁, t₂, h₂, h⟩ : (1 : Set α) ∈ f * g := hfg.symm ▸ one_mem_one
    have hfg : (f * g).NeBot := hfg.symm.subst one_neBot
    rw [(hfg.nonempty_of_mem <| mul_mem_mul h₁ h₂).subset_one_iff, Set.mul_eq_one_iff] at h
    obtain ⟨a, b, rfl, rfl, h⟩ := h
    refine ⟨a, b, ?_, ?_, h⟩
    · rwa [← hfg.of_mul_left.le_pure_iff, le_pure_iff]
    · rwa [← hfg.of_mul_right.le_pure_iff, le_pure_iff]
  · rintro ⟨a, b, rfl, rfl, h⟩
    rw [pure_mul_pure, h, pure_one]

/-- `Filter α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`Filter α` is a subtraction monoid under pointwise operations if
 `α` is."]
protected def divisionMonoid : DivisionMonoid (Filter α) :=
  { Filter.monoid, Filter.instInvolutiveInv, Filter.instDiv, Filter.instZPow (α := α) with
    mul_inv_rev := fun s t => map_map₂_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Filter.mul_eq_one_iff.1 h
      rw [inv_pure, inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun f g => map_map₂_distrib_right div_eq_mul_inv }

@[to_additive]
theorem isUnit_iff : IsUnit f ↔ ∃ a, f = pure a ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Filter.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, pure_injective ?_⟩, rfl⟩
    rw [← pure_mul_pure, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.filter

end DivisionMonoid

/-- `Filter α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtractionCommMonoid
      "`Filter α` is a commutative subtraction monoid under pointwise operations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Filter α) :=
  { Filter.divisionMonoid, Filter.commSemigroup with }

/-- `Filter α` has distributive negation if `α` has. -/
protected def instDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Filter α) :=
  { Filter.instInvolutiveNeg with
    neg_mul := fun _ _ => map₂_map_left_comm neg_mul
    mul_neg := fun _ _ => map_map₂_right_comm mul_neg }

scoped[Pointwise] attribute [instance] Filter.commMonoid Filter.addCommMonoid Filter.divisionMonoid
  Filter.subtractionMonoid Filter.divisionCommMonoid Filter.subtractionCommMonoid
  Filter.instDistribNeg

section Distrib

variable [Distrib α] {f g h : Filter α}

/-!
Note that `Filter α` is not a `Distrib` because `f * g + f * h` has cross terms that `f * (g + h)`
lacks.
-/

theorem mul_add_subset : f * (g + h) ≤ f * g + f * h :=
  map₂_distrib_le_left mul_add

theorem add_mul_subset : (f + g) * h ≤ f * h + g * h :=
  map₂_distrib_le_right add_mul

end Distrib

section MulZeroClass

variable [MulZeroClass α] {f g : Filter α}

/-! Note that `Filter` is not a `MulZeroClass` because `0 * ⊥ ≠ 0`. -/

theorem NeBot.mul_zero_nonneg (hf : f.NeBot) : 0 ≤ f * 0 :=
  le_mul_iff.2 fun _ h₁ _ h₂ =>
    let ⟨_, ha⟩ := hf.nonempty_of_mem h₁
    ⟨_, ha, _, h₂, mul_zero _⟩

theorem NeBot.zero_mul_nonneg (hg : g.NeBot) : 0 ≤ 0 * g :=
  le_mul_iff.2 fun _ h₁ _ h₂ =>
    let ⟨_, hb⟩ := hg.nonempty_of_mem h₂
    ⟨_, h₁, _, hb, zero_mul _⟩

end MulZeroClass

section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]
  (m : F) {f g f₁ g₁ : Filter α} {f₂ g₂ : Filter β}

/-! Note that `Filter α` is not a group because `f / f ≠ 1` in general -/

-- Porting note: increase priority to appease `simpNF` so left-hand side doesn't simplify
@[to_additive (attr := simp 1100)]
protected theorem one_le_div_iff : 1 ≤ f / g ↔ ¬Disjoint f g := by
  refine ⟨fun h hfg => ?_, ?_⟩
  · obtain ⟨s, hs, t, ht, hst⟩ := hfg.le_bot (mem_bot : ∅ ∈ ⊥)
    exact Set.one_mem_div_iff.1 (h <| div_mem_div hs ht) (disjoint_iff.2 hst.symm)
  · rintro h s ⟨t₁, h₁, t₂, h₂, hs⟩
    exact hs (Set.one_mem_div_iff.2 fun ht => h <| disjoint_of_disjoint_of_mem ht h₁ h₂)

@[to_additive]
theorem not_one_le_div_iff : ¬1 ≤ f / g ↔ Disjoint f g :=
  Filter.one_le_div_iff.not_left

@[to_additive]
theorem NeBot.one_le_div (h : f.NeBot) : 1 ≤ f / f := by
  rintro s ⟨t₁, h₁, t₂, h₂, hs⟩
  obtain ⟨a, ha₁, ha₂⟩ := Set.not_disjoint_iff.1 (h.not_disjoint h₁ h₂)
  rw [mem_one, ← div_self' a]
  exact hs (Set.div_mem_div ha₁ ha₂)

@[to_additive]
theorem isUnit_pure (a : α) : IsUnit (pure a : Filter α) :=
  (Group.isUnit a).filter

@[simp]
theorem isUnit_iff_singleton : IsUnit f ↔ ∃ a, f = pure a := by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[to_additive]
theorem map_inv' : f⁻¹.map m = (f.map m)⁻¹ :=
  Semiconj.filter_map (map_inv m) f

@[to_additive]
protected theorem Tendsto.inv_inv : Tendsto m f₁ f₂ → Tendsto m f₁⁻¹ f₂⁻¹ := fun hf =>
  (Filter.map_inv' m).trans_le <| Filter.inv_le_inv hf

@[to_additive]
protected theorem map_div : (f / g).map m = f.map m / g.map m :=
  map_map₂_distrib <| map_div m

@[to_additive]
protected theorem Tendsto.div_div (hf : Tendsto m f₁ f₂) (hg : Tendsto m g₁ g₂) :
    Tendsto m (f₁ / g₁) (f₂ / g₂) :=
  (Filter.map_div m).trans_le <| Filter.div_le_div hf hg

end Group

open Pointwise

section GroupWithZero

variable [GroupWithZero α] {f g : Filter α}

theorem NeBot.div_zero_nonneg (hf : f.NeBot) : 0 ≤ f / 0 :=
  Filter.le_div_iff.2 fun _ h₁ _ h₂ =>
    let ⟨_, ha⟩ := hf.nonempty_of_mem h₁
    ⟨_, ha, _, h₂, div_zero _⟩

theorem NeBot.zero_div_nonneg (hg : g.NeBot) : 0 ≤ 0 / g :=
  Filter.le_div_iff.2 fun _ h₁ _ h₂ =>
    let ⟨_, hb⟩ := hg.nonempty_of_mem h₂
    ⟨_, h₁, _, hb, zero_div _⟩

end GroupWithZero

/-! ### Scalar addition/multiplication of filters -/


section SMul

variable [SMul α β] {f f₁ f₂ : Filter α} {g g₁ g₂ h : Filter β} {s : Set α} {t : Set β} {a : α}
  {b : β}

/-- The filter `f • g` is generated by `{s • t | s ∈ f, t ∈ g}` in locale `Pointwise`. -/
@[to_additive "The filter `f +ᵥ g` is generated by `{s +ᵥ t | s ∈ f, t ∈ g}` in locale
 `Pointwise`."]
protected def instSMul : SMul (Filter α) (Filter β) :=
  ⟨/- This is defeq to `map₂ (· • ·) f g`, but the hypothesis unfolds to `t₁ • t₂ ⊆ s`
  rather than all the way to `Set.image2 (· • ·) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· • ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ • t₂ ⊆ s } }⟩

scoped[Pointwise] attribute [instance] Filter.instSMul Filter.instVAdd

@[to_additive (attr := simp)]
theorem map₂_smul : map₂ (· • ·) f g = f • g :=
  rfl

@[to_additive]
theorem mem_smul : t ∈ f • g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ • t₂ ⊆ t :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul : s ∈ f → t ∈ g → s • t ∈ f • g :=
  image2_mem_map₂

@[to_additive (attr := simp)]
theorem bot_smul : (⊥ : Filter α) • g = ⊥ :=
  map₂_bot_left

@[to_additive (attr := simp)]
theorem smul_bot : f • (⊥ : Filter β) = ⊥ :=
  map₂_bot_right

@[to_additive (attr := simp)]
theorem smul_eq_bot_iff : f • g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
  map₂_eq_bot_iff

@[to_additive (attr := simp)]
theorem smul_neBot_iff : (f • g).NeBot ↔ f.NeBot ∧ g.NeBot :=
  map₂_neBot_iff

@[to_additive]
protected theorem NeBot.smul : NeBot f → NeBot g → NeBot (f • g) :=
  NeBot.map₂

@[to_additive]
theorem NeBot.of_smul_left : (f • g).NeBot → f.NeBot :=
  NeBot.of_map₂_left

@[to_additive]
theorem NeBot.of_smul_right : (f • g).NeBot → g.NeBot :=
  NeBot.of_map₂_right

@[to_additive vadd.instNeBot]
lemma smul.instNeBot [NeBot f] [NeBot g] : NeBot (f • g) := .smul ‹_› ‹_›

scoped[Pointwise] attribute [instance] smul.instNeBot vadd.instNeBot

@[to_additive (attr := simp)]
theorem pure_smul : (pure a : Filter α) • g = g.map (a • ·) :=
  map₂_pure_left

@[to_additive (attr := simp)]
theorem smul_pure : f • pure b = f.map (· • b) :=
  map₂_pure_right

@[to_additive]
-- Porting note (#11119): removed `simp` attribute because `simpNF` says it can prove it.
theorem pure_smul_pure : (pure a : Filter α) • (pure b : Filter β) = pure (a • b) :=
  map₂_pure

@[to_additive]
theorem smul_le_smul : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ • g₁ ≤ f₂ • g₂ :=
  map₂_mono

@[to_additive]
theorem smul_le_smul_left : g₁ ≤ g₂ → f • g₁ ≤ f • g₂ :=
  map₂_mono_left

@[to_additive]
theorem smul_le_smul_right : f₁ ≤ f₂ → f₁ • g ≤ f₂ • g :=
  map₂_mono_right

@[to_additive (attr := simp)]
theorem le_smul_iff : h ≤ f • g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s • t ∈ h :=
  le_map₂_iff

@[to_additive]
instance covariant_smul : CovariantClass (Filter α) (Filter β) (· • ·) (· ≤ ·) :=
  ⟨fun _ _ _ => map₂_mono_left⟩

end SMul

/-! ### Scalar subtraction of filters -/


section Vsub

variable [VSub α β] {f f₁ f₂ g g₁ g₂ : Filter β} {h : Filter α} {s t : Set β} {a b : β}

/-- The filter `f -ᵥ g` is generated by `{s -ᵥ t | s ∈ f, t ∈ g}` in locale `Pointwise`. -/
protected def instVSub : VSub (Filter α) (Filter β) :=
  ⟨/- This is defeq to `map₂ (-ᵥ) f g`, but the hypothesis unfolds to `t₁ -ᵥ t₂ ⊆ s` rather than all
  the way to `Set.image2 (-ᵥ) t₁ t₂ ⊆ s`. -/
  fun f g => { map₂ (· -ᵥ ·) f g with sets := { s | ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ -ᵥ t₂ ⊆ s } }⟩

scoped[Pointwise] attribute [instance] Filter.instVSub

@[simp]
theorem map₂_vsub : map₂ (· -ᵥ ·) f g = f -ᵥ g :=
  rfl

theorem mem_vsub {s : Set α} : s ∈ f -ᵥ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ -ᵥ t₂ ⊆ s :=
  Iff.rfl

theorem vsub_mem_vsub : s ∈ f → t ∈ g → s -ᵥ t ∈ f -ᵥ g :=
  image2_mem_map₂

@[simp]
theorem bot_vsub : (⊥ : Filter β) -ᵥ g = ⊥ :=
  map₂_bot_left

@[simp]
theorem vsub_bot : f -ᵥ (⊥ : Filter β) = ⊥ :=
  map₂_bot_right

@[simp]
theorem vsub_eq_bot_iff : f -ᵥ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
  map₂_eq_bot_iff

@[simp]
theorem vsub_neBot_iff : (f -ᵥ g : Filter α).NeBot ↔ f.NeBot ∧ g.NeBot :=
  map₂_neBot_iff

protected theorem NeBot.vsub : NeBot f → NeBot g → NeBot (f -ᵥ g) :=
  NeBot.map₂

theorem NeBot.of_vsub_left : (f -ᵥ g : Filter α).NeBot → f.NeBot :=
  NeBot.of_map₂_left

theorem NeBot.of_vsub_right : (f -ᵥ g : Filter α).NeBot → g.NeBot :=
  NeBot.of_map₂_right

lemma vsub.instNeBot [NeBot f] [NeBot g] : NeBot (f -ᵥ g) := .vsub ‹_› ‹_›

scoped[Pointwise] attribute [instance] vsub.instNeBot

@[simp]
theorem pure_vsub : (pure a : Filter β) -ᵥ g = g.map (a -ᵥ ·) :=
  map₂_pure_left

@[simp]
theorem vsub_pure : f -ᵥ pure b = f.map (· -ᵥ b) :=
  map₂_pure_right

-- Porting note (#11119): removed `simp` attribute because `simpNF` says it can prove it.
theorem pure_vsub_pure : (pure a : Filter β) -ᵥ pure b = (pure (a -ᵥ b) : Filter α) :=
  map₂_pure

theorem vsub_le_vsub : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ -ᵥ g₁ ≤ f₂ -ᵥ g₂ :=
  map₂_mono

theorem vsub_le_vsub_left : g₁ ≤ g₂ → f -ᵥ g₁ ≤ f -ᵥ g₂ :=
  map₂_mono_left

theorem vsub_le_vsub_right : f₁ ≤ f₂ → f₁ -ᵥ g ≤ f₂ -ᵥ g :=
  map₂_mono_right

@[simp]
theorem le_vsub_iff : h ≤ f -ᵥ g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s -ᵥ t ∈ h :=
  le_map₂_iff

end Vsub

/-! ### Translation/scaling of filters -/


section SMul

variable [SMul α β] {f f₁ f₂ : Filter β} {s : Set β} {a : α}

/-- `a • f` is the map of `f` under `a •` in locale `Pointwise`. -/
@[to_additive "`a +ᵥ f` is the map of `f` under `a +ᵥ` in locale `Pointwise`."]
protected def instSMulFilter : SMul α (Filter β) :=
  ⟨fun a => map (a • ·)⟩

scoped[Pointwise] attribute [instance] Filter.instSMulFilter Filter.instVAddFilter

@[to_additive (attr := simp)]
protected theorem map_smul : map (fun b => a • b) f = a • f :=
  rfl

@[to_additive]
theorem mem_smul_filter : s ∈ a • f ↔ (a • ·) ⁻¹' s ∈ f := Iff.rfl

@[to_additive]
theorem smul_set_mem_smul_filter : s ∈ f → a • s ∈ a • f :=
  image_mem_map

@[to_additive (attr := simp)]
theorem smul_filter_bot : a • (⊥ : Filter β) = ⊥ :=
  map_bot

@[to_additive (attr := simp)]
theorem smul_filter_eq_bot_iff : a • f = ⊥ ↔ f = ⊥ :=
  map_eq_bot_iff

@[to_additive (attr := simp)]
theorem smul_filter_neBot_iff : (a • f).NeBot ↔ f.NeBot :=
  map_neBot_iff _

@[to_additive]
theorem NeBot.smul_filter : f.NeBot → (a • f).NeBot := fun h => h.map _

@[to_additive]
theorem NeBot.of_smul_filter : (a • f).NeBot → f.NeBot :=
  NeBot.of_map

@[to_additive vadd_filter.instNeBot]
lemma smul_filter.instNeBot [NeBot f] : NeBot (a • f) := .smul_filter ‹_›

scoped[Pointwise] attribute [instance] smul_filter.instNeBot vadd_filter.instNeBot

@[to_additive]
theorem smul_filter_le_smul_filter (hf : f₁ ≤ f₂) : a • f₁ ≤ a • f₂ :=
  map_mono hf

@[to_additive]
instance covariant_smul_filter : CovariantClass α (Filter β) (· • ·) (· ≤ ·) :=
  ⟨fun _ => @map_mono β β _⟩

end SMul

open Pointwise

@[to_additive]
instance smulCommClass_filter [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Filter γ) :=
  ⟨fun _ _ _ => map_comm (funext <| smul_comm _ _) _⟩

@[to_additive]
instance smulCommClass_filter' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Filter β) (Filter γ) :=
  ⟨fun a _ _ => map_map₂_distrib_right <| smul_comm a⟩

@[to_additive]
instance smulCommClass_filter'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Filter α) β (Filter γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Filter α) (Filter β) (Filter γ) :=
  ⟨fun _ _ _ => map₂_left_comm smul_comm⟩

@[to_additive vaddAssocClass]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Filter γ) :=
  ⟨fun a b f => by simp only [← Filter.map_smul, map_map, smul_assoc]; rfl⟩

@[to_additive vaddAssocClass']
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Filter β) (Filter γ) :=
  ⟨fun a f g => by
    refine (map_map₂_distrib_left fun _ _ => ?_).symm
    exact (smul_assoc a _ _).symm⟩

@[to_additive vaddAssocClass'']
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Filter α) (Filter β) (Filter γ) :=
  ⟨fun _ _ _ => map₂_assoc smul_assoc⟩

@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Filter β) :=
  ⟨fun _ f => (congr_arg fun m => map m f) <| funext fun _ => op_smul_eq_smul _ _⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`Filter α` on `Filter β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
 of `Filter α` on `Filter β`"]
protected def mulAction [Monoid α] [MulAction α β] : MulAction (Filter α) (Filter β) where
  one_smul f := map₂_pure_left.trans <| by simp_rw [one_smul, map_id']
  mul_smul f g h := map₂_assoc mul_smul

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Filter β`.
-/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action on
 `Filter β`."]
protected def mulActionFilter [Monoid α] [MulAction α β] : MulAction α (Filter β) where
  mul_smul a b f := by simp only [← Filter.map_smul, map_map, Function.comp_def, ← mul_smul]
  one_smul f := by simp only [← Filter.map_smul, one_smul, map_id']

scoped[Pointwise] attribute [instance] Filter.mulAction Filter.addAction Filter.mulActionFilter
  Filter.addActionFilter

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Filter β`. -/
protected def distribMulActionFilter [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Filter β) where
  smul_add _ _ _ := map_map₂_distrib <| smul_add _
  smul_zero _ := (map_pure _ _).trans <| by rw [smul_zero, pure_zero]

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
protected def mulDistribMulActionFilter [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]

scoped[Pointwise]
  attribute [instance] Filter.distribMulActionFilter Filter.mulDistribMulActionFilter

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {f : Filter α} {g : Filter β}

/-!
Note that we have neither `SMulWithZero α (Filter β)` nor `SMulWithZero (Filter α) (Filter β)`
because `0 * ⊥ ≠ 0`.
-/

theorem NeBot.smul_zero_nonneg (hf : f.NeBot) : 0 ≤ f • (0 : Filter β) :=
  le_smul_iff.2 fun _ h₁ _ h₂ =>
    let ⟨_, ha⟩ := hf.nonempty_of_mem h₁
    ⟨_, ha, _, h₂, smul_zero _⟩

theorem NeBot.zero_smul_nonneg (hg : g.NeBot) : 0 ≤ (0 : Filter α) • g :=
  le_smul_iff.2 fun _ h₁ _ h₂ =>
    let ⟨_, hb⟩ := hg.nonempty_of_mem h₂
    ⟨_, h₁, _, hb, zero_smul _ _⟩

theorem zero_smul_filter_nonpos : (0 : α) • g ≤ 0 := by
  refine fun s hs => mem_smul_filter.2 ?_
  convert @univ_mem _ g
  refine eq_univ_iff_forall.2 fun a => ?_
  rwa [mem_preimage, zero_smul]

theorem zero_smul_filter (hg : g.NeBot) : (0 : α) • g = 0 :=
  zero_smul_filter_nonpos.antisymm <|
    le_map_iff.2 fun s hs => by
      simp_rw [zero_smul, (hg.nonempty_of_mem hs).image_const]
      exact zero_mem_zero

end SMulWithZero

end Filter

/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Order
import Mathlib.GroupTheory.Submonoid.Membership

#align_import data.rat.star from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-! # Star order structure on ℚ

Here we put the trivial `star` operation on `ℚ` for convenience and show that it is a
`StarOrderedRing`. In particular, this means that every element of `ℚ` is a sum of squares.
-/


namespace Rat

instance : StarRing ℚ where
  star := id
  star_involutive _ := rfl
  star_mul _ _ := mul_comm _ _
  star_add _ _ := rfl

instance : TrivialStar ℚ where star_trivial _ := rfl

instance : StarOrderedRing ℚ :=
  StarOrderedRing.ofNonnegIff (fun {_ _} => add_le_add_left) fun x => by
    refine'
      ⟨fun hx => _, fun hx =>
        AddSubmonoid.closure_induction hx (by rintro - ⟨s, rfl⟩; exact mul_self_nonneg s) le_rfl
          fun _ _ => add_nonneg⟩
    /- If `x = p / q`, then, since `0 ≤ x`, we have `p q : ℕ`, and `p / q` is the sum of `p * q`
      copies of `(1 / q) ^ 2`, and so `x` lies in the `AddSubmonoid` generated by square elements.

      Note: it's possible to rephrase this argument as `x = (p * q) • (1 / q) ^ 2`, but this would
      be somewhat challenging without increasing import requirements. -/
    -- Porting note: rewrote proof to avoid removed constructor rat.mk_pnat
    suffices
      (Finset.range (x.num.natAbs * x.den)).sum
          (Function.const ℕ ((1 : ℚ) / x.den * ((1 : ℚ) / x.den))) =
        x
      by exact this ▸ sum_mem fun n _ => AddSubmonoid.subset_closure ⟨_, rfl⟩
    simp only [Function.const_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Int.cast_ofNat, Int.ofNat_mul, Int.coe_natAbs,
      abs_of_nonneg (num_nonneg.mpr hx), Int.cast_mul, Int.cast_ofNat]
    rw [← mul_assoc, mul_assoc (x.num : ℚ), mul_one_div_cancel (Nat.cast_ne_zero.mpr x.pos.ne'),
      mul_one, mul_one_div, Rat.num_div_den]
end Rat

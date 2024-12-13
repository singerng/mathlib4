/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
-- HEAD
import Mathlib.Algebra.Ring.Rat
import Mathlib.SetTheory.Cardinal.Basic
--
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Logic.Denumerable
-- master

/-!
# Denumerability of ℚ

This file proves that ℚ is denumerable.

The fact that ℚ has cardinality ℵ₀ is proved in `Mathlib.Data.Rat.Cardinal`
-/

assert_not_exists Module
assert_not_exists Field

namespace Rat

open Denumerable

/-- **Denumerability of the Rational Numbers** -/
instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ

end Rat

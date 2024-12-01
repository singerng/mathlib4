/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib

section def1

class IsMoritaEquivalent
  (R : Type*) (S : Type*) [Ring R] [Ring S] : Prop where
out : Nonempty <| ModuleCat R ≌ ModuleCat S

variable (F A : Type*) [Field F] [Ring A] [Algebra F A]

class IsQuaternionAlgebra (Q : Type*) [Ring Q] [Algebra F Q] extends
    Algebra.IsCentral F Q where
  rank_four : Module.finrank F Q = 4
  simple : IsSimpleRing Q

variable [hA : IsQuaternionAlgebra F A]

end def1

-- -- /-! space -/

-- /-- Quaternion algebra over a type with fixed coefficients $a=i^2$ and $b=j^2$.
-- Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`. -/
-- @[ext]
-- structure QuaternionAlgebra (R : Type*) (a b c : R) where
--   /-- Real part of a quaternion. -/
--   re : R
--   /-- First imaginary part (i) of a quaternion. -/
--   imI : R
--   /-- Second imaginary part (j) of a quaternion. -/
--   imJ : R
--   /-- Third imaginary part (k) of a quaternion. -/
--   imK : R

-- @[inherit_doc]
-- scoped[Quaternion] notation "ℍ[" R "," a "," b ", " c "]" =>
--     QuaternionAlgebra R a b c

-- open Quaternion

-- namespace QuaternionAlgebra

-- /-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
-- @[simps]
-- def equivProd {R : Type*} (c₁ c₂ c₃: R) : ℍ[R,c₁,c₂, c₃] ≃ R × R × R × R where
--   toFun a := ⟨a.1, a.2, a.3, a.4⟩
--   invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
--   left_inv _ := rfl
--   right_inv _ := rfl

-- /-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
-- @[simps symm_apply]
-- def equivTuple {R : Type*} (c₁ c₂ c₃: R) : ℍ[R,c₁,c₂, c₃] ≃ (Fin 4 → R) where
--   toFun a := ![a.1, a.2, a.3, a.4]
--   invFun a := ⟨a 0, a 1, a 2, a 3⟩
--   left_inv _ := rfl
--   right_inv f := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

-- @[simp]
-- theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃: R) (x : ℍ[R,c₁,c₂, c₃]) :
--     equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] :=
--   rfl

-- @[simp]
-- theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂, c₃]) :
--     mk a.1 a.2 a.3 a.4 = a := rfl


-- variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y z : R) (a b c : ℍ[R,c₁,c₂, c₃])
-- instance [Subsingleton R] : Subsingleton ℍ[R,c₁,c₂, c₃] := (equivTuple _ _ _).subsingleton
-- instance [Nontrivial R] : Nontrivial ℍ[R, c₁, c₂, c₃] := (equivTuple _ _ _).surjective.nontrivial

-- section Zero
-- variable [Zero R]

-- /-- The imaginary part of a quaternion. -/
-- def im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃] :=
--   ⟨0, x.imI, x.imJ, x.imK⟩

-- @[simp]
-- theorem im_re : a.im.re = 0 :=
--   rfl

-- @[simp]
-- theorem im_imI : a.im.imI = a.imI :=
--   rfl

-- @[simp]
-- theorem im_imJ : a.im.imJ = a.imJ :=
--   rfl

-- @[simp]
-- theorem im_imK : a.im.imK = a.imK :=
--   rfl

-- @[simp]
-- theorem im_idem : a.im.im = a.im :=
--   rfl


-- /-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
-- @[coe] def coe (x : R) : ℍ[R,c₁,c₂,c₃] := ⟨x, 0, 0, 0⟩

-- instance : CoeTC R ℍ[R,c₁,c₂,c₃] := ⟨coe⟩

-- @[simp, norm_cast]
-- theorem coe_re : (x : ℍ[R,c₁,c₂,c₃]).re = x := rfl

-- @[simp, norm_cast]
-- theorem coe_imI : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

-- @[simp, norm_cast]
-- theorem coe_imJ : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

-- @[simp, norm_cast]
-- theorem coe_imK : (x : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

-- theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂,c₃]) :=
    --fun _ _ h => congr_arg re h

-- @[simp]
-- theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y :=
--   coe_injective.eq_iff

-- -- Porting note: removed `simps`, added simp lemmas manually
-- instance : Zero ℍ[R,c₁,c₂,c₃] := ⟨⟨0, 0, 0, 0⟩⟩

-- @[simp] theorem zero_re : (0 : ℍ[R,c₁,c₂,c₃]).re = 0 := rfl

-- @[simp] theorem zero_imI : (0 : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

-- @[simp] theorem zero_imJ : (0 : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

-- @[simp] theorem zero_imK : (0 : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

-- @[simp] theorem zero_im : (0 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

-- @[simp, norm_cast]
-- theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0 := rfl

-- instance : Inhabited ℍ[R,c₁,c₂,c₃] := ⟨0⟩

-- section One
-- variable [One R]
-- -- Porting note: removed `simps`, added simp lemmas manually
-- instance : One ℍ[R,c₁,c₂,c₃] := ⟨⟨1, 0, 0, 0⟩⟩

-- @[simp] theorem one_re : (1 : ℍ[R,c₁,c₂,c₃]).re = 1 := rfl

-- @[simp] theorem one_imI : (1 : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

-- @[simp] theorem one_imJ : (1 : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

-- @[simp] theorem one_imK : (1 : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

-- @[simp] theorem one_im : (1 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

-- @[simp, norm_cast]
-- theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1 := rfl

-- end One

-- end Zero

-- section Add
-- variable [Add R]

-- -- Porting note: removed `simps`, added simp lemmas manually
-- instance : Add ℍ[R,c₁,c₂,c₃] :=
--   ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

-- @[simp] theorem add_re : (a + b).re = a.re + b.re := rfl

-- @[simp] theorem add_imI : (a + b).imI = a.imI + b.imI := rfl

-- @[simp] theorem add_imJ : (a + b).imJ = a.imJ + b.imJ := rfl

-- @[simp] theorem add_imK : (a + b).imK = a.imK + b.imK := rfl

-- @[simp]
-- theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
--     (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + mk b₁ b₂ b₃ b₄ =
--     mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
--   rfl

-- end Add

-- section AddZeroClass
-- variable [AddZeroClass R]

-- @[simp] theorem add_im : (a + b).im = a.im + b.im :=
--   QuaternionAlgebra.ext (zero_add _).symm rfl rfl rfl

-- @[simp, norm_cast]
-- theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y := by ext <;> simp

-- end AddZeroClass

-- section Neg
-- variable [Neg R]

-- -- Porting note: removed `simps`, added simp lemmas manually
-- instance : Neg ℍ[R,c₁,c₂,c₃] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

-- @[simp] theorem neg_re : (-a).re = -a.re := rfl

-- @[simp] theorem neg_imI : (-a).imI = -a.imI := rfl

-- @[simp] theorem neg_imJ : (-a).imJ = -a.imJ := rfl

-- @[simp] theorem neg_imK : (-a).imK = -a.imK := rfl

-- @[simp]
-- theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
--   rfl

-- end Neg

-- section AddGroup
-- variable [AddGroup R]

-- @[simp] theorem neg_im : (-a).im = -a.im :=
--   QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl
-- @[simp, norm_cast]
-- theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x := by ext <;> simp

-- instance : Sub ℍ[R,c₁,c₂,c₃] :=
--   ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩
-- @[simp] theorem sub_re : (a - b).re = a.re - b.re := rfl

-- @[simp] theorem sub_imI : (a - b).imI = a.imI - b.imI := rfl
-- @[simp] theorem sub_imJ : (a - b).imJ = a.imJ - b.imJ := rfl

-- @[simp] theorem sub_imK : (a - b).imK = a.imK - b.imK := rfl
-- @[simp] theorem sub_im : (a - b).im = a.im - b.im :=
--   QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl

-- @[simp]
-- theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
--     (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) - mk b₁ b₂ b₃ b₄ =
--     mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
--   rfl

-- @[simp, norm_cast]
-- theorem coe_im : (x : ℍ[R,c₁,c₂,c₃]).im = 0 :=
--   rfl

-- @[simp]
-- theorem re_add_im : ↑a.re + a.im = a :=
--   QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

-- @[simp]
-- theorem sub_self_im : a - a.im = a.re :=
--   QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

-- @[simp]
-- theorem sub_self_re : a - a.re = a.im :=
--   QuaternionAlgebra.ext (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

-- end AddGroup

-- section Ring
-- variable [Ring R]

-- /-- Multiplication is given by
-- ## Needs fixing
--  -/
-- instance : Mul ℍ[R,c₁,c₂,c₃] :=
--   ⟨fun a b =>
--     ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
--     a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
--     a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
--     a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

-- @[simp]
-- theorem mul_re : (a * b).re = a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 +
--     c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4 := rfl

-- @[simp]
-- theorem mul_imI : (a * b).imI = a.1 * b.2 + a.2 * b.1 +
--     c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3 := rfl

-- @[simp]
-- theorem mul_imJ : (a * b).imJ = a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 +
--     c₂ * a.3 * b.2 - c₁ * a.4 * b.2 := rfl

-- @[simp]
-- theorem mul_imK : (a * b).imK = a.1 * b.4 + a.2 * b.3 +
--     c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1 := rfl

-- @[simp]
-- theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
--     (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) * mk b₁ b₂ b₃ b₄ =
--     mk (a₁ * b₁ + c₁ * a₂ * b₂ + c₂ * a₃ * b₃ + c₂ * c₃ * a₃ * b₄ - c₁ * c₃ * a₄ * b₄)
--     (a₁ * b₂ + a₂ * b₁ + c₂ * a₂ * b₂ - c₃ * a₃ * b₄ + c₃ * a₄ * b₃)
--     (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ + c₂ * a₃ * b₂ - c₁ * a₄ * b₂)
--     (a₁ * b₄ + a₂ * b₃ + c₂ * a₂ * b₄ - a₃ * b₂ + a₄ * b₁) :=
--   rfl

-- end Ring
-- section SMul

-- variable [SMul S R] [SMul T R] (s : S)

-- instance : SMul S ℍ[R,c₁,c₂, c₃] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

-- instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
--   smul_assoc s t x := by ext <;> exact smul_assoc _ _ _

-- instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
--   smul_comm s t x := by ext <;> exact smul_comm _ _ _

-- @[simp] theorem smul_re : (s • a).re = s • a.re := rfl

-- @[simp] theorem smul_imI : (s • a).imI = s • a.imI := rfl

-- @[simp] theorem smul_imJ : (s • a).imJ = s • a.imJ := rfl

-- @[simp] theorem smul_imK : (s • a).imK = s • a.imK := rfl

-- @[simp] theorem smul_im {S} [CommRing R] [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
--   QuaternionAlgebra.ext (smul_zero s).symm rfl rfl rfl

-- @[simp]
-- theorem smul_mk (re im_i im_j im_k : R) :
--     s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
--   rfl

-- end SMul

-- @[simp, norm_cast]
-- theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
--     (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃]) :=
--   QuaternionAlgebra.ext rfl (smul_zero s).symm (smul_zero s).symm (smul_zero s).symm

-- instance [AddCommGroup R] : AddCommGroup ℍ[R,c₁,c₂,c₃] :=
--   (equivProd c₁ c₂ c₃).injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
--     (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

-- section AddCommGroupWithOne
-- variable [AddCommGroupWithOne R]

-- instance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃] where
--   natCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
--   natCast_zero := by simp
--   natCast_succ := by simp
--   intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
--   intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
--   intCast_negSucc n := by
--     change coe _ = -coe _
--     rw [Int.cast_negSucc, coe_neg]

-- @[simp, norm_cast]
-- theorem natCast_re (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).re = n :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias nat_cast_re := natCast_re

-- @[simp, norm_cast]
-- theorem natCast_imI (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias nat_cast_imI := natCast_imI

-- @[simp, norm_cast]
-- theorem natCast_imJ (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias nat_cast_imJ := natCast_imJ

-- @[simp, norm_cast]
-- theorem natCast_imK (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias nat_cast_imK := natCast_imK

-- @[simp, norm_cast]
-- theorem natCast_im (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).im = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias nat_cast_im := natCast_im

-- @[norm_cast]
-- theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃]) :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias coe_nat_cast := coe_natCast

-- @[simp, norm_cast]
-- theorem intCast_re (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).re = z :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias int_cast_re := intCast_re

-- @[simp, norm_cast]
-- theorem intCast_imI (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias int_cast_imI := intCast_imI

-- @[simp, norm_cast]
-- theorem intCast_imJ (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias int_cast_imJ := intCast_imJ

-- @[simp, norm_cast]
-- theorem intCast_imK (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias int_cast_imK := intCast_imK

-- @[simp, norm_cast]
-- theorem intCast_im (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).im = 0 :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias int_cast_im := intCast_im

-- @[norm_cast]
-- theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃]) :=
--   rfl

-- @[deprecated (since := "2024-04-17")]
-- alias coe_int_cast := coe_intCast

-- end AddCommGroupWithOne

-- -- For the remainder of the file we assume `CommRing R`.
-- variable [CommRing R]

-- instance instRing : Ring ℍ[R,c₁,c₂,c₃] where
--   __ := inferInstanceAs (AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
--   left_distrib _ _ _ := by ext <;> simp <;> ring
--   right_distrib _ _ _ := by ext <;> simp <;> ring
--   zero_mul _ := by ext <;> simp
--   mul_zero _ := by ext <;> simp
--   mul_assoc α β γ := by
--     ext
--     · simp only [mul_re, mul_imI, mul_imJ, mul_imK]
--       simp only [sub_mul, add_mul, mul_add, mul_sub, ← mul_assoc]
--       rw [add_assoc, ← add_sub, ← add_sub, add_assoc, add_assoc, add_assoc, add_assoc]
--       symm
--       rw [← add_sub, ← add_sub, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc,
--         add_right_inj]
--       symm
--       rw [add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm, add_comm,
--         add_comm, add_comm, add_comm]
--       nth_rw 1 [sub_add, ← add_assoc, add_sub, sub_add, add_comm]
--       nth_rw 2 [sub_add]
--       rw [sub_sub, sub_sub, ← sub_add]
--       nth_rw 1 [← add_sub]
--       rw [add_comm]; nth_rw 3 [mul_comm]
--       rw [← add_sub, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc]
--       symm; rw [add_assoc, add_right_inj]; symm
--       nth_rw 1 [add_comm]; nth_rw 2 [add_comm]
--       nth_rw 3 [add_comm, mul_comm]
--       rw [← add_sub, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc,
--         add_assoc, add_right_inj]
--       ring_nf!
--       rw [add_comm (c₂ * c₁ * α.imI * β.imK * γ.imJ)]
--       symm; rw [sub_eq_add_neg]; simp only [add_assoc, add_right_inj]
--       rw [add_comm]; nth_rw 2 [add_comm]; symm
--       rw [add_comm]; nth_rw 2 [add_comm]; simp only [add_assoc, add_right_inj]

--       sorry
--     · sorry
--     · sorry
--     · sorry
--   one_mul _ := by ext <;> simp
--   mul_one _ := by ext <;> simp
-- #check sub_eq_add_neg
-- @[norm_cast, simp]
-- theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂, c₃]) = x * y := by ext <;> simp

-- -- -- TODO: add weaker `MulAction`, `DistribMulAction`, and `Module` instances (and repeat them
-- -- -- for `ℍ[R]`)
-- instance [CommSemiring S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂,c₃] where
--   smul := (· • ·)
--   toFun s := coe (algebraMap S R s)
--   map_one' := by simp only [map_one, coe_one]
--   map_zero' := by simp only [map_zero, coe_zero]
--   map_mul' x y := by simp only [map_mul, coe_mul]
--   map_add' x y := by simp only [map_add, coe_add]
--   smul_def' s x := by ext <;> simp [Algebra.smul_def]
--   commutes' s x := by ext <;> simp [Algebra.commutes]

-- theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩ :=
--   rfl

-- theorem algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ → _).Injective :=
--   fun _ _ ↦ by simp [algebraMap_eq]

-- instance [NoZeroDivisors R] : NoZeroSMulDivisors R ℍ[R,c₁,c₂,c₃] := ⟨by
--   rintro t ⟨a, b, c, d⟩ h
--   rw [or_iff_not_imp_left]
--   intro ht
--   simpa [QuaternionAlgebra.ext_iff, ht] using h⟩

-- section

-- variable (c₁ c₂ c₃)

-- /-- `QuaternionAlgebra.re` as a `LinearMap`-/
-- @[simps]
-- def reₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
--   toFun := re
--   map_add' _ _ := rfl
--   map_smul' _ _ := rfl

-- /-- `QuaternionAlgebra.imI` as a `LinearMap`-/
-- @[simps]
-- def imIₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
--   toFun := imI
--   map_add' _ _ := rfl
--   map_smul' _ _ := rfl

-- /-- `QuaternionAlgebra.imJ` as a `LinearMap`-/
-- @[simps]
-- def imJₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
--   toFun := imJ
--   map_add' _ _ := rfl
--   map_smul' _ _ := rfl

-- /-- `QuaternionAlgebra.imK` as a `LinearMap`-/
-- @[simps]
-- def imKₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
--   toFun := imK
--   map_add' _ _ := rfl
--   map_smul' _ _ := rfl

-- /-- `QuaternionAlgebra.equivTuple` as a linear equivalence. -/
-- def linearEquivTuple : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 → R :=
--   LinearEquiv.symm -- proofs are not `rfl` in the forward direction
--     { (equivTuple c₁ c₂ c₃).symm with
--       toFun := (equivTuple c₁ c₂ c₃).symm
--       invFun := equivTuple c₁ c₂ _
--       map_add' := fun _ _ => rfl
--       map_smul' := fun _ _ => rfl }

-- @[simp]
-- theorem coe_linearEquivTuple : ⇑(linearEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ :=
--   rfl

-- @[simp]
-- theorem coe_linearEquivTuple_symm : ⇑(linearEquivTuple c₁ c₂ c₃).symm =
--     (equivTuple c₁ c₂ c₃).symm :=
--   rfl

-- /-- `ℍ[R, c₁, c₂]` has a basis over `R` given by `1`, `i`, `j`, and `k`. -/
-- noncomputable def basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃] :=
--   .ofEquivFun <| linearEquivTuple c₁ c₂ _

-- @[simp]
-- theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) :
--     ⇑((basisOneIJK c₁ c₂ c₃).repr q) = ![q.re, q.imI, q.imJ, q.imK] :=
--   rfl

-- instance : Module.Finite R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ _)

-- instance : Module.Free R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ _)

-- theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4 := by
--   rw [rank_eq_card_basis (basisOneIJK c₁ c₂ _), Fintype.card_fin]
--   norm_num

-- theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
--   rw [Module.finrank, rank_eq_four, Cardinal.toNat_ofNat]

-- -- /-- There is a natural equivalence when swapping the coefficients of a quaternion algebra. -/
-- -- @[simps]
-- -- def swapEquiv : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₂,c₁,c₃] where
-- --   toFun t := ⟨t.1, t.3, t.2, -t.4⟩
-- --   invFun t := ⟨t.1, t.3, t.2, -t.4⟩
-- --   left_inv _ := by simp
-- --   right_inv _ := by simp
-- --   map_mul' a b := by
-- --     ext <;> simp only [mul_re, mul_imJ, mul_imI, add_left_inj, mul_imK, neg_mul, neg_add_rev,
-- --                      neg_sub, mk_mul_mk, mul_neg, neg_neg, sub_neg_eq_add]
-- --     · simp only [add_assoc]
-- --       rw [← add_sub, ← add_sub, ← add_sub, ← add_sub, add_right_inj]
-- --       symm; rw [← add_assoc]; nth_rw 2 [add_comm]
-- --       rw [add_assoc, ← add_sub, add_right_inj, ← add_sub, add_right_inj]

-- --       sorry
-- --     · sorry
-- --     · sorry
-- --     · sorry

-- --   map_add' _ _ := by ext <;> simp [add_comm]
-- --   commutes' _ := by simp [algebraMap_eq]

-- end

-- @[norm_cast, simp]
-- theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y :=
--   (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

-- @[norm_cast, simp]
-- theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n :=
--   (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n

-- theorem coe_commutes : ↑r * a = a * r :=
--   Algebra.commutes r a

-- theorem coe_commute : Commute (↑r) a :=
--   coe_commutes r a

-- theorem coe_mul_eq_smul : ↑r * a = r • a :=
--   (Algebra.smul_def r a).symm

-- theorem mul_coe_eq_smul : a * r = r • a := by rw [← coe_commutes, coe_mul_eq_smul]

-- @[norm_cast, simp]
-- theorem coe_algebraMap : ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe :=
--   rfl

-- theorem smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]

-- /-- Quaternion conjugate. -/
-- instance instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂,c₃] where star a :=
--     ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩

-- @[simp] theorem re_star : (star a).re = a.re + c₂ * a.imI := rfl

-- @[simp]
-- theorem imI_star : (star a).imI = -a.imI :=
--   rfl

-- @[simp]
-- theorem imJ_star : (star a).imJ = -a.imJ :=
--   rfl

-- @[simp]
-- theorem imK_star : (star a).imK = -a.imK :=
--   rfl

-- @[simp]
-- theorem im_star : (star a).im = -a.im :=
--   QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

-- @[simp]
-- theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
--     ⟨a₁ + c₂ * a₂, -a₂, -a₃, -a₄⟩ :=
--   rfl

-- instance instStarRing : StarRing ℍ[R,c₁,c₂,c₃] where
--   star_involutive x := by simp [Star.star]
--   star_add a b := by
--     ext <;> simp [add_comm]
--     simp only [add_assoc, add_right_inj]
--     symm
--     rw [← add_assoc, add_comm (c₂ * a.imI)]
--     ring
--   star_mul a b := by ext <;> simp <;> ring


-- theorem self_add_star' : a + star a = ↑(2 * a.re + c₂ * a.imI) := by ext <;> simp [two_mul]; ring

-- theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by
--   simp [self_add_star', two_mul]

-- theorem star_add_self' : star a + a = ↑(2 * a.re + c₂ * a.imI) := by
    --rw [add_comm, self_add_star']

-- theorem star_add_self : star a + a = 2 * a.re + c₂ * a.imI := by rw [add_comm, self_add_star]

-- theorem star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a :=
--   eq_sub_iff_add_eq.2 a.star_add_self'

-- instance : IsStarNormal a :=
--   ⟨by
--     delta Commute; delta SemiconjBy
--     rw [a.star_eq_two_re_sub]
--     ext <;> simp <;> ring⟩


-- @[simp, norm_cast]
-- theorem star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x := by ext <;> simp

-- @[simp] theorem star_im : star a.im = -a.im + c₂ * a.imI := by
--   rw [← im_star a]
--   ext <;> simp

-- @[simp]
-- theorem star_smul [CommRing S] [Algebra S R] (s : S) (a : ℍ[R,c₁,c₂,c₃]) :
--     star (s • a) = s • star a :=
--   QuaternionAlgebra.ext (by aesop) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

-- theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re := by rw [h, coe_re]

-- theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} :
--     a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R,c₁,c₂,c₃]) :=
--   ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩


-- section CharZero

-- variable [NoZeroDivisors R] [CharZero R]

-- @[simp]
-- theorem star_eq_self {c₁ c₂ c₃: R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re := by
--   simp [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]
--   tauto

-- -- theorem star_eq_neg {c₁ c₂ c₃: R} {a : ℍ[R,c₁,c₂,c₃]} : star a = -a ↔ a.re = 0 := by
-- --   simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

-- end CharZero

-- -- Can't use `rw ← star_eq_self` in the proof without additional assumptions
-- theorem star_mul_eq_coe : star a * a = (star a * a).re := by ext <;> simp <;> ring

-- theorem mul_star_eq_coe : a * star a = (a * star a).re := by
--   rw [← star_comm_self']
--   exact a.star_mul_eq_coe

-- open MulOpposite

-- /-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
-- def starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ :=
--   { starAddEquiv.trans opAddEquiv with
--     toFun := op ∘ star
--     invFun := star ∘ unop
--     map_mul' := fun x y => by simp
--     commutes' := fun r => by simp }

-- @[simp]
-- theorem coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star :=
--   rfl

-- end QuaternionAlgebra

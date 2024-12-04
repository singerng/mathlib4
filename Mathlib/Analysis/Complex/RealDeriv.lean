/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Complex.Basic

/-! # Real differentiability of complex-differentiable functions

`HasDerivAt.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/

assert_not_exists IsConformalMap
assert_not_exists Conformal

section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/

open Complex

variable {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) :
    HasStrictDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasStrictFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasStrictFDerivAt
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasStrictFDerivAt.restrictScalars ℝ
  have C : HasStrictFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasStrictFDerivAt
  -- Porting note: this should be by:
  -- simpa using (C.comp z (B.comp z A)).hasStrictDerivAt
  -- but for some reason simp can not use `ContinuousLinearMap.comp_apply`
  convert (C.comp z (B.comp z A)).hasStrictDerivAt
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp

/-- If a complex function `e` is differentiable at a real point, then the function `ℝ → ℝ` given by
the real part of `e` is also differentiable at this point, with a derivative equal to the real part
of the complex derivative. -/
theorem HasDerivAt.real_of_complex (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasFDerivAt
  -- Porting note: this should be by:
  -- simpa using (C.comp z (B.comp z A)).hasStrictDerivAt
  -- but for some reason simp can not use `ContinuousLinearMap.comp_apply`
  convert (C.comp z (B.comp z A)).hasDerivAt
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp

theorem ContDiffAt.real_of_complex {n : WithTop ℕ∞} (h : ContDiffAt ℂ n e z) :
    ContDiffAt ℝ n (fun x : ℝ => (e x).re) z := by
  have A : ContDiffAt ℝ n ((↑) : ℝ → ℂ) z := ofRealCLM.contDiff.contDiffAt
  have B : ContDiffAt ℝ n e z := h.restrict_scalars ℝ
  have C : ContDiffAt ℝ n re (e z) := reCLM.contDiff.contDiffAt
  exact C.comp z (B.comp z A)

theorem ContDiff.real_of_complex {n : WithTop ℕ∞} (h : ContDiff ℂ n e) :
    ContDiff ℝ n fun x : ℝ => (e x).re :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem HasStrictDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using
    h.hasStrictFDerivAt.restrictScalars ℝ

theorem HasDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
    HasFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using h.hasFDerivAt.restrictScalars ℝ

theorem HasDerivWithinAt.complexToReal_fderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (reCLM.smulRight f' + I • imCLM.smulRight f') s x := by
  simpa only [Complex.restrictScalars_one_smulRight'] using
    h.hasFDerivWithinAt.restrictScalars ℝ

theorem HasStrictDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasStrictFDerivAt.restrictScalars ℝ

theorem HasDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
    HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasFDerivAt.restrictScalars ℝ

theorem HasDerivWithinAt.complexToReal_fderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ}
    (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x := by
  simpa only [Complex.restrictScalars_one_smulRight] using h.hasFDerivWithinAt.restrictScalars ℝ

/-- If a complex function `e` is differentiable at a real point, then its restriction to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative. -/
theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z := by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using hf.comp z ofRealCLM.hasDerivAt

/-- If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is also
differentiable as a function `ℝ → ℂ`. -/
theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using
    ofRealCLM.hasDerivAt.scomp z hf

-- theorem hasDerivAt_ofReal_comp_iff {f : ℝ → ℝ} {u : ℝ} :
--     HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z ↔ HasDerivAt f u z:=
--   ⟨fun h ↦ by simpa only [reCLM_apply, ofReal_re] using reCLM.hasFDerivAt.comp_hasDerivAt z h,
--     fun h ↦ HasDerivAt.ofReal_comp h⟩

-- theorem differentiableAt_ofReal_comp_iff {f : ℝ → ℝ} :
--     DifferentiableAt ℝ (fun y : ℝ => ↑(f y) : ℝ → ℂ) z ↔ DifferentiableAt ℝ f z := by
--   refine ⟨?_, ?_⟩
--   · intro h



--     rw [← hasDerivAt_deriv_iff] at h
--     have := HasDerivAt.real_of_complex (e := fun y : ℂ ↦ f y.re) (z := z)
--       (e' := deriv (fun y ↦ ↑(f y)) z) ?_
--     simp at this
--     exact HasFDerivAt.differentiableAt this
--     have :=  HasFDerivAt.comp_hasDerivAt (f := re)
--   · intro h
--     rw [← hasDerivAt_deriv_iff] at h
--     have := h.ofReal_comp
--     exact HasFDerivAt.differentiableAt this


-- theorem Complex.ofReal_deriv (f : ℝ → ℝ) :
--     (fun x ↦ ↑(deriv f x)) = deriv (fun x ↦ (f x : ℂ)) := by
--   ext x
--   by_cases h : DifferentiableAt ℝ f x
--   · rw [← hasDerivAt_deriv_iff] at h
--     have := HasDerivAt.ofReal_comp h
--     rw [HasDerivAt.deriv this]
--   · rw [deriv_zero_of_not_differentiableAt h]
--     rw [← differentiableAt_ofReal_comp_iff] at h
--     rw [deriv_zero_of_not_differentiableAt h, Complex.ofReal_zero]


-- #exit

--   rw [deriv, fderiv]
--   split_ifs with h
--   · obtain ⟨f', hf⟩ := h
--     have := hf.hasDerivAt.ofReal_comp
--     have := HasDerivAt.deriv this
--     rw [this]

--     sorry
--   · sorry

end RealDerivOfComplex

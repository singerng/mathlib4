/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `MDifferentiable`, `ContMDiff`, `mfderiv`, `tangentMap`
and related notions.

## Main statements

* `ContMDiffOn.contMDiffOn_tangentMapWithin` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `ContMDiff.contMDiff_tangentMap` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/

open Set Function Filter ChartedSpace SmoothManifoldWithCorners Bundle

open scoped Topology Manifold Bundle

/-! ### Definition of smooth functions between manifolds -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [Js : SmoothManifoldWithCorners J N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- declare functions, sets, points and smoothness indices
  {f : M → M'}
  {s : Set M} {m n : ℕ∞}

-- Porting note: section about deducing differentiability from smoothness moved to
-- `Geometry.Manifold.MFDeriv.Basic`

/-! ### The derivative of a smooth function is smooth -/

section mfderiv
variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']

/-- The function that sends `x` to the `y`-derivative of `f (x, y)` at `g (x)` is `C^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is `C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
Version within a set.
-/
protected theorem ContMDiffWithinAt.mfderivWithin {x₀ : N} {f : N → M → M'} {g : N → M}
    {t : Set N} {u : Set M}
    (hf : ContMDiffWithinAt (J.prod I) I' n (Function.uncurry f) (t ×ˢ u) (x₀, g x₀))
    (hg : ContMDiffWithinAt J I m g t x₀) (hx₀ : x₀ ∈ t)
    (hu : MapsTo g t u) (hmn : m + 1 ≤ n) (h'u : UniqueMDiffOn I u) :
    ContMDiffWithinAt J 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' g (fun x => f x (g x))
        (fun x => mfderivWithin I I' (f x) u (g x)) x₀) t x₀ := by
  let t' := t ∩ g ⁻¹' ((extChartAt I (g x₀)).source)
  have ht't : t' ⊆ t := inter_subset_left
  suffices ContMDiffWithinAt J 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' g (fun x ↦ f x (g x))
        (fun x ↦ mfderivWithin I I' (f x) u (g x)) x₀) t' x₀ by
    apply ContMDiffWithinAt.mono_of_mem this
    apply inter_mem self_mem_nhdsWithin
    exact hg.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds I (g x₀))
  have hx₀gx₀ : (x₀, g x₀) ∈ t ×ˢ u := by simp [hx₀, hu hx₀]
  have h4f : ContinuousWithinAt (fun x => f x (g x)) t x₀ := by
    change ContinuousWithinAt ((Function.uncurry f) ∘ (fun x ↦ (x, g x))) t x₀
    refine ContinuousWithinAt.comp hf.continuousWithinAt ?_ (fun y hy ↦ by simp [hy, hu hy])
    exact (continuousWithinAt_id.prod hg.continuousWithinAt)
  have h4f := h4f.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds I' (f x₀ (g x₀)))
  have h3f := contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin.mp
    (hf.of_le <| (self_le_add_left 1 m).trans hmn)
  simp only [Nat.cast_one, hx₀gx₀, insert_eq_of_mem] at h3f
  have h2f : ∀ᶠ x₂ in 𝓝[t] x₀, ContMDiffWithinAt I I' 1 (f x₂) u (g x₂) := by
    have : MapsTo (fun x ↦ (x, g x)) t (t ×ˢ u) := fun y hy ↦ by simp [hy, hu hy]
    filter_upwards [((continuousWithinAt_id.prod hg.continuousWithinAt)
      |>.tendsto_nhdsWithin this).eventually h3f, self_mem_nhdsWithin] with x hx h'x
    apply hx.comp (g x) (contMDiffWithinAt_const.prod_mk contMDiffWithinAt_id)
    exact fun y hy ↦ by simp [h'x, hy]
  have h2g : g ⁻¹' (extChartAt I (g x₀)).source ∈ 𝓝[t] x₀ :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds I (g x₀))
  have : ContDiffWithinAt 𝕜 m (fun x ↦ fderivWithin 𝕜
        (extChartAt I' (f x₀ (g x₀)) ∘ f ((extChartAt J x₀).symm x) ∘ (extChartAt I (g x₀)).symm)
        ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
        (extChartAt I (g x₀) (g ((extChartAt J x₀).symm x))))
      ((extChartAt J x₀).symm ⁻¹' t' ∩ range J) (extChartAt J x₀ x₀) := by
    have hf' := hf.mono (prod_mono_left ht't)
    have hg' := hg.mono (show t' ⊆ t from inter_subset_left)
    rw [contMDiffWithinAt_iff] at hf' hg'
    simp_rw [Function.comp_def, uncurry, extChartAt_prod, PartialEquiv.prod_coe_symm,
      ModelWithCorners.range_prod] at hf' ⊢
    apply ContDiffWithinAt.fderivWithin _ _ _ hmn
    · simp [hx₀, t']
    · apply inter_subset_left.trans
      rw [preimage_subset_iff]
      intro a ha
      refine ⟨PartialEquiv.map_source _ (inter_subset_right ha : _), ?_⟩
      rw [mem_preimage, PartialEquiv.left_inv (extChartAt I (g x₀))]
      · exact hu (inter_subset_left ha)
      · exact (inter_subset_right ha :)
    · have : ((fun p ↦ ((extChartAt J x₀).symm p.1, (extChartAt I (g x₀)).symm p.2)) ⁻¹' t' ×ˢ u
            ∩ range J ×ˢ (extChartAt I (g x₀)).target)
          ⊆ ((fun p ↦ ((extChartAt J x₀).symm p.1, (extChartAt I (g x₀)).symm p.2)) ⁻¹' t' ×ˢ u
            ∩ range J ×ˢ range I) := by
        apply inter_subset_inter_right
        exact Set.prod_mono_right (extChartAt_target_subset_range I (g x₀))
      convert hf'.2.mono this
      · ext y; simp; tauto
      · simp
    · exact hg'.2
    · exact UniqueMDiffOn.uniqueDiffOn_target_inter h'u (g x₀)
  have :
    ContMDiffWithinAt J 𝓘(𝕜, E →L[𝕜] E') m
      (fun x =>
        fderivWithin 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ f x ∘ (extChartAt I (g x₀)).symm)
        ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
          (extChartAt I (g x₀) (g x))) t' x₀ := by
    simp_rw [contMDiffWithinAt_iff_source_of_mem_source (mem_chart_source G x₀),
      contMDiffWithinAt_iff_contDiffWithinAt, Function.comp_def] at this ⊢
    exact this
  apply this.congr_of_eventuallyEq_of_mem _ (by simp [t', hx₀])
  apply nhdsWithin_mono _ ht't
  filter_upwards [h2f, h4f, h2g, self_mem_nhdsWithin] with x hx h'x h2 hxt
  have h1 : g x ∈ u := hu hxt
  have h3 : UniqueMDiffWithinAt 𝓘(𝕜, E)
      ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
      ((extChartAt I (g x₀)) (g x)) := by
    apply UniqueDiffWithinAt.uniqueMDiffWithinAt
    apply UniqueMDiffOn.uniqueDiffOn_target_inter h'u
    refine ⟨PartialEquiv.map_source _ h2, ?_⟩
    rwa [mem_preimage, PartialEquiv.left_inv _ h2]
  have A : mfderivWithin 𝓘(𝕜, E) I ((extChartAt I (g x₀)).symm)
        (range I) ((extChartAt I (g x₀)) (g x))
      = mfderivWithin 𝓘(𝕜, E) I ((extChartAt I (g x₀)).symm)
        ((extChartAt I (g x₀)).target ∩ (extChartAt I (g x₀)).symm ⁻¹' u)
        ((extChartAt I (g x₀)) (g x)) := by
    apply (MDifferentiableWithinAt.mfderivWithin_mono _ h3 _).symm
    · apply mdifferentiableWithinAt_extChartAt_symm
      exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
    · exact inter_subset_left.trans (extChartAt_target_subset_range I (g x₀))
  rw [inTangentCoordinates_eq_mfderiv_comp, A,
    ← mfderivWithin_comp_of_eq, ← mfderiv_comp_mfderivWithin_of_eq]
  · exact mfderivWithin_eq_fderivWithin
  · exact mdifferentiableAt_extChartAt (by simpa using h'x)
  · apply MDifferentiableWithinAt.comp (I' := I) (u := u) _ _ _ inter_subset_right
    · convert hx.mdifferentiableWithinAt le_rfl
      exact PartialEquiv.left_inv (extChartAt I (g x₀)) h2
    · apply (mdifferentiableWithinAt_extChartAt_symm _).mono
      · exact inter_subset_left.trans (extChartAt_target_subset_range I (g x₀))
      · exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
  · exact h3
  · simp only [Function.comp_def, PartialEquiv.left_inv (extChartAt I (g x₀)) h2]
  · exact hx.mdifferentiableWithinAt le_rfl
  · apply (mdifferentiableWithinAt_extChartAt_symm _).mono
    · exact inter_subset_left.trans (extChartAt_target_subset_range I (g x₀))
    · exact PartialEquiv.map_source (extChartAt I (g x₀)) h2
  · exact inter_subset_right
  · exact h3
  · exact PartialEquiv.left_inv (extChartAt I (g x₀)) h2
  · simpa using h2
  · simpa using h'x

/-- The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `ContMDiffWithinAt.mfderivWithin` where `f` does not contain any
parameters and `g = id`.
-/
theorem ContMDiffWithinAt.mfderivWithin_const {x₀ : M} {f : M → M'}
    (hf : ContMDiffWithinAt I I' n f s x₀)
    (hmn : m + 1 ≤ n) (hx : x₀ ∈ s) (hs : UniqueMDiffOn I s) :
    ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' id f (mfderivWithin I I' f s) x₀) s x₀ := by
  have : ContMDiffWithinAt (I.prod I) I' n (fun x : M × M => f x.2) (s ×ˢ s) (x₀, x₀) :=
    ContMDiffWithinAt.comp (x₀, x₀) hf contMDiffWithinAt_snd mapsTo_snd_prod
  exact this.mfderivWithin contMDiffWithinAt_id hx (mapsTo_id _) hmn hs

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivative sensible.

This is similar to `ContMDiffWithinAt.mfderivWithin`, but where the continuous linear map is
applied to a (variable) vector.
-/
theorem ContMDiffWithinAt.mfderivWithin_apply {x₀ : N'}
    {f : N → M → M'} {g : N → M} {g₁ : N' → N} {g₂ : N' → E} {t : Set N} {u : Set M} {v : Set N'}
    (hf : ContMDiffWithinAt (J.prod I) I' n (Function.uncurry f) (t ×ˢ u) (g₁ x₀, g (g₁ x₀)))
    (hg : ContMDiffWithinAt J I m g t (g₁ x₀)) (hg₁ : ContMDiffWithinAt J' J m g₁ v x₀)
    (hg₂ : ContMDiffWithinAt J' 𝓘(𝕜, E) m g₂ v x₀) (hmn : m + 1 ≤ n) (h'g₁ : MapsTo g₁ v t)
    (hg₁x₀ : g₁ x₀ ∈ t) (h'g : MapsTo g t u) (hu : UniqueMDiffOn I u) :
    ContMDiffWithinAt J' 𝓘(𝕜, E') m
      (fun x => (inTangentCoordinates I I' g (fun x => f x (g x))
        (fun x => mfderivWithin I I' (f x) u (g x)) (g₁ x₀) (g₁ x)) (g₂ x)) v x₀ :=
  ((hf.mfderivWithin hg hg₁x₀ h'g hmn hu).comp_of_eq hg₁ h'g₁ rfl).clm_apply hg₂

/-- The function that sends `x` to the `y`-derivative of `f (x, y)` at `g (x)` is `C^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is `C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This result is used to show that maps into the 1-jet bundle and cotangent bundle are smooth.
`ContMDiffAt.mfderiv_const` is a special case of this.
-/
protected theorem ContMDiffAt.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (x₀, g x₀)) (hg : ContMDiffAt J I m g x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' g (fun x ↦ f x (g x)) (fun x ↦ mfderiv I I' (f x) (g x)) x₀)
      x₀ := by
  rw [← contMDiffWithinAt_univ] at hf hg ⊢
  rw [← univ_prod_univ] at hf
  simp_rw [← mfderivWithin_univ]
  exact ContMDiffWithinAt.mfderivWithin hf hg (mem_univ _) (mapsTo_univ _ _) hmn
    uniqueMDiffOn_univ

/-- The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `ContMDiffAt.mfderiv` where `f` does not contain any parameters and
`g = id`.
-/
theorem ContMDiffAt.mfderiv_const {x₀ : M} {f : M → M'} (hf : ContMDiffAt I I' n f x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E') m (inTangentCoordinates I I' id f (mfderiv I I' f) x₀) x₀ :=
  haveI : ContMDiffAt (I.prod I) I' n (fun x : M × M => f x.2) (x₀, x₀) :=
    ContMDiffAt.comp (x₀, x₀) hf contMDiffAt_snd
  this.mfderiv (fun _ => f) id contMDiffAt_id hmn

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivative sensible.

This is similar to `ContMDiffAt.mfderiv`, but where the continuous linear map is applied to a
(variable) vector.
-/
theorem ContMDiffAt.mfderiv_apply {x₀ : N'} (f : N → M → M') (g : N → M) (g₁ : N' → N) (g₂ : N' → E)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (g₁ x₀, g (g₁ x₀)))
    (hg : ContMDiffAt J I m g (g₁ x₀)) (hg₁ : ContMDiffAt J' J m g₁ x₀)
    (hg₂ : ContMDiffAt J' 𝓘(𝕜, E) m g₂ x₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt J' 𝓘(𝕜, E') m
      (fun x => inTangentCoordinates I I' g (fun x => f x (g x))
        (fun x => mfderiv I I' (f x) (g x)) (g₁ x₀) (g₁ x) (g₂ x)) x₀ :=
  ((hf.mfderiv f g hg hmn).comp_of_eq hg₁ rfl).clm_apply hg₂

end mfderiv

/-! ### The tangent map of a smooth function is smooth -/

section tangentMap

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem ContMDiffOn.contMDiffOn_tangentMapWithin
    [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']
    (hf : ContMDiffOn I I' n f s) (hmn : m + 1 ≤ n)
    (hs : UniqueMDiffOn I s) :
    ContMDiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s)
      (π E (TangentSpace I) ⁻¹' s) := by
  intro x₀ hx₀
  let s' : Set (TangentBundle I M) := (π E (TangentSpace I) ⁻¹' s)
  let b₁ : TangentBundle I M → M := fun p ↦ p.1
  let v : Π (y : TangentBundle I M), TangentSpace I (b₁ y) := fun y ↦ y.2
  have hv : ContMDiffWithinAt I.tangent I.tangent m (fun y ↦ (v y : TangentBundle I M)) s' x₀ :=
    contMDiffWithinAt_id
  let b₂ : TangentBundle I M → M' := f ∘ b₁
  have hb₂ : ContMDiffWithinAt I.tangent I' m b₂ s' x₀ :=
    ((hf (b₁ x₀) hx₀).of_le (le_self_add.trans hmn)).comp _
      (contMDiffWithinAt_proj (TangentSpace I)) (fun x h ↦ h)
  let ϕ : Π (y : TangentBundle I M), TangentSpace I (b₁ y) →L[𝕜] TangentSpace I' (b₂ y) :=
    fun y ↦ mfderivWithin I I' f s (b₁ y)
  have hϕ : ContMDiffWithinAt I.tangent 𝓘(𝕜, E →L[𝕜] E') m
      (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
        (TangentSpace I' (M := M')) (b₁ x₀) (b₁ y) (b₂ x₀) (b₂ y) (ϕ y))
      s' x₀ := by
    have A : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') m
        (fun y ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I (M := M)) E'
          (TangentSpace I' (M := M')) (b₁ x₀) y (b₂ x₀) (f y) (mfderivWithin I I' f s y))
        s (b₁ x₀) :=
      ContMDiffWithinAt.mfderivWithin_const (hf _ hx₀) hmn hx₀ hs
    exact A.comp _ (contMDiffWithinAt_proj (TangentSpace I)) (fun x h ↦ h)
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

@[deprecated (since := "2024-10-07")]
alias ContMDiffOn.contMDiffOn_tangentMapWithin_aux := ContMDiffOn.contMDiffOn_tangentMapWithin

@[deprecated (since := "2024-10-07")]
alias ContMDiffOn.continuousOn_tangentMapWithin_aux := ContMDiffOn.contMDiffOn_tangentMapWithin

variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem ContMDiffOn.continuousOn_tangentMapWithin (hf : ContMDiffOn I I' n f s) (hmn : 1 ≤ n)
    (hs : UniqueMDiffOn I s) :
    ContinuousOn (tangentMapWithin I I' f s) (π E (TangentSpace I) ⁻¹' s) :=
  haveI :
    ContMDiffOn I.tangent I'.tangent 0 (tangentMapWithin I I' f s) (π E (TangentSpace I) ⁻¹' s) :=
    hf.contMDiffOn_tangentMapWithin hmn hs
  this.continuousOn

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem ContMDiff.contMDiff_tangentMap (hf : ContMDiff I I' n f) (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent I'.tangent m (tangentMap I I' f) := by
  rw [← contMDiffOn_univ] at hf ⊢
  convert hf.contMDiffOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem ContMDiff.continuous_tangentMap (hf : ContMDiff I I' n f) (hmn : 1 ≤ n) :
    Continuous (tangentMap I I' f) := by
  rw [← contMDiffOn_univ] at hf
  rw [continuous_iff_continuousOn_univ]
  convert hf.continuousOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]

/-- If a function is smooth, then its bundled derivative is smooth. -/
theorem Smooth.tangentMap (hf : Smooth I I' f) :
    Smooth I.tangent I'.tangent (tangentMap I I' f) :=
  ContMDiff.contMDiff_tangentMap hf le_rfl

end tangentMap

namespace TangentBundle

open Bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
theorem tangentMap_tangentBundle_pure [Is : SmoothManifoldWithCorners I M] (p : TangentBundle I M) :
    tangentMap I I.tangent (zeroSection E (TangentSpace I)) p = ⟨⟨p.proj, 0⟩, ⟨p.2, 0⟩⟩ := by
  rcases p with ⟨x, v⟩
  have N : I.symm ⁻¹' (chartAt H x).target ∈ 𝓝 (I ((chartAt H x) x)) := by
    apply IsOpen.mem_nhds
    · apply (PartialHomeomorph.open_target _).preimage I.continuous_invFun
    · simp only [mfld_simps]
  have A : MDifferentiableAt I I.tangent (fun x => @TotalSpace.mk M E (TangentSpace I) x 0) x :=
    haveI : Smooth I (I.prod 𝓘(𝕜, E)) (zeroSection E (TangentSpace I : M → Type _)) :=
      Bundle.smooth_zeroSection 𝕜 (TangentSpace I : M → Type _)
    this.mdifferentiableAt
  have B : fderivWithin 𝕜 (fun x' : E ↦ (x', (0 : E))) (Set.range I) (I ((chartAt H x) x)) v
      = (v, 0) := by
    rw [fderivWithin_eq_fderiv, DifferentiableAt.fderiv_prod]
    · simp
    · exact differentiableAt_id'
    · exact differentiableAt_const _
    · exact ModelWithCorners.uniqueDiffWithinAt_image I
    · exact differentiableAt_id'.prod (differentiableAt_const _)
  simp (config := { unfoldPartialApp := true }) only [Bundle.zeroSection, tangentMap, mfderiv, A,
    if_pos, chartAt, FiberBundle.chartedSpace_chartAt, TangentBundle.trivializationAt_apply,
    tangentBundleCore, Function.comp_def, ContinuousLinearMap.map_zero, mfld_simps]
  rw [← fderivWithin_inter N] at B
  rw [← fderivWithin_inter N, ← B]
  congr 1
  refine fderivWithin_congr (fun y hy => ?_) ?_
  · simp only [mfld_simps] at hy
    simp only [hy, Prod.mk.inj_iff, mfld_simps]
  · simp only [Prod.mk.inj_iff, mfld_simps]

end TangentBundle

namespace ContMDiffMap

-- These helpers for dot notation have been moved here from
-- `Mathlib/Geometry/Manifold/ContMDiffMap.lean` to avoid needing to import this file there.
-- (However as a consequence we import `Mathlib/Geometry/Manifold/ContMDiffMap.lean` here now.)
-- They could be moved to another file (perhaps a new file) if desired.
open scoped Manifold

protected theorem mdifferentiable' (f : C^n⟮I, M; I', M'⟯) (hn : 1 ≤ n) : MDifferentiable I I' f :=
  f.contMDiff.mdifferentiable hn

protected theorem mdifferentiable (f : C^∞⟮I, M; I', M'⟯) : MDifferentiable I I' f :=
  f.contMDiff.mdifferentiable le_top

protected theorem mdifferentiableAt (f : C^∞⟮I, M; I', M'⟯) {x} : MDifferentiableAt I I' f x :=
  f.mdifferentiable x

end ContMDiffMap

section EquivTangentBundleProd

variable (I I' M M') in
/-- The tangent bundle of a product is canonically isomorphic to the product of the tangent
bundles. -/
@[simps] def equivTangentBundleProd :
    TangentBundle (I.prod I') (M × M') ≃ (TangentBundle I M) × (TangentBundle I' M') where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma equivTangentBundleProd_eq_tangentMap_prod_tangentMap :
    equivTangentBundleProd I M I' M' = fun (p : TangentBundle (I.prod I') (M × M')) ↦
      (tangentMap (I.prod I') I Prod.fst p, tangentMap (I.prod I') I' Prod.snd p) := by
  simp only [tangentMap_prod_fst, tangentMap_prod_snd]; rfl

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']

/-- The canonical equivalence between the tangent bundle of a product and the product of
tangent bundles is smooth. -/
lemma smooth_equivTangentBundleProd :
    Smooth (I.prod I').tangent (I.tangent.prod I'.tangent) (equivTangentBundleProd I M I' M') := by
  rw [equivTangentBundleProd_eq_tangentMap_prod_tangentMap]
  exact smooth_fst.tangentMap.prod_mk smooth_snd.tangentMap

/-- The canonical equivalence between the product of tangent bundles and the tangent bundle of a
product is smooth. -/
lemma smooth_equivTangentBundleProd_symm :
    Smooth (I.tangent.prod I'.tangent) (I.prod I').tangent
      (equivTangentBundleProd I M I' M').symm := by
  /- I am really unhappy with this proof, but I haven't found a more functorial one, so I have to
  unfold more definitions than I'd like. The argument goes as follows: since we're looking at a
  map into a vector bundle whose basis map is smooth, it suffices to check the smoothness of the
  second coordinate. We're in a product, so it suffices to check that each projection is smooth.
  We notice that the first projection is the composition of the tangent map to `(x : M) ↦ (x, b.2)`
  with obvious extensions or restrictions, and the tangent map to a smooth map is smooth, so we're
  done.
  The issue is with checking differentiability everywhere (to justify that the derivative of a
  product is the product of the derivatives), and writing down things.
  -/
  simp only [Smooth, ContMDiff, Prod.forall]
  intro a b
  rw [contMDiffAt_totalSpace]
  simp only [equivTangentBundleProd, Equiv.coe_fn_symm_mk, TangentBundle.trivializationAt_apply,
    PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
    PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
    modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
    ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
    ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
    PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply]
  refine ⟨?_, (contMDiffAt_prod_module_iff _).2 ⟨?_, ?_⟩⟩
  · exact ContMDiffAt.prod_map (smoothAt_proj (TangentSpace I)) (smoothAt_proj (TangentSpace I'))
  · -- check that, in the fiber, the first projection is smooth in charts
    -- for this, write down a map which is obviously smooth (`C` below) and then check that the two
    -- maps coincide, up to obvious compositions.
    have C : ContMDiffAt I.tangent (I.prod I').tangent ⊤ (fun (p : TangentBundle I M)
        ↦ (⟨(p.1, b.1), (p.2, 0)⟩ : TangentBundle (I.prod I') (M × M'))) a := by
      let f : M → M × M' := fun m ↦ (m, b.1)
      have A : Smooth I.tangent (I.prod I').tangent (tangentMap I (I.prod I') f) := by
        apply Smooth.tangentMap
        exact smooth_id.prod_mk smooth_const
      have B : tangentMap I (I.prod I') f = fun p ↦ ⟨(p.1, b.1), (p.2, 0)⟩ := by
        ext p : 1
        exact tangentMap_prod_left I I'
      rw [B] at A
      exact A a
    have Z := ((contMDiffAt_totalSpace _ _).1 C).2
    simp only [modelWithCornersSelf_prod, TangentBundle.trivializationAt_apply,
      PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
      modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
      ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
      PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply] at Z
    have D1 : ContMDiff (𝓘(𝕜, E × E')) (𝓘(𝕜, E)) ⊤ (Prod.fst : E × E' → E) := by
      rw [contMDiff_iff_contDiff]; exact contDiff_fst
    have D2 : ContMDiffAt (I.tangent.prod I'.tangent) I.tangent ⊤ Prod.fst (a, b) := smoothAt_fst
    have U' := (ContMDiffAt.comp a D1.contMDiffAt Z).comp (a, b) D2
    apply U'.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds (ModelProd (ModelProd H E) (ModelProd H' E')) (a, b)]
      with p hp
    clear U' D1 D2 C Z
    simp only [prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod_source, Set.mem_prod, TangentBundle.mem_chart_source_iff] at hp
    let φ (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
    have D0 : DifferentiableWithinAt 𝕜 φ (Set.range I) (I ((chartAt H p.1.proj) p.1.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp [hp.1]
    have D (w : TangentBundle I' M') :
        DifferentiableWithinAt 𝕜 (φ ∘ (Prod.fst : E × E' → E)) (Set.range (Prod.map ↑I ↑I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' w.proj) w.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0)
        differentiableWithinAt_fst (by simp [mapsTo_fst_prod])
    let φ' (x : E') := I' ((chartAt H' b.proj) ((chartAt H' b.proj).symm (I'.symm x)))
    have D0' : DifferentiableWithinAt 𝕜 φ' (Set.range I')
        (I' ((chartAt H' b.proj) b.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp
    have D' : DifferentiableWithinAt 𝕜 (φ' ∘ Prod.snd) (Set.range (Prod.map I I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' b.proj) b.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0') differentiableWithinAt_snd
        (by simp [mapsTo_snd_prod])
    have U w : UniqueDiffWithinAt 𝕜 (Set.range (Prod.map I I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' w) := by
      simp only [Set.range_prod_map]
      apply UniqueDiffWithinAt.prod
      · exact ModelWithCorners.uniqueDiffWithinAt_image I
      · exact ModelWithCorners.uniqueDiffWithinAt_image I'
    simp only [Set.range_prod_map, ContinuousLinearMap.prod_apply, comp_def, comp_apply]
    rw [DifferentiableWithinAt.fderivWithin_prod (by exact D _) ?_ (U _)]; swap
    · let φ'' (x : E') := I' ((chartAt H' b.proj) ((chartAt H' p.2.proj).symm (I'.symm x)))
      have D0' : DifferentiableWithinAt 𝕜 φ'' (Set.range I')
          (I' ((chartAt H' p.2.proj) p.2.proj)) := by
        apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
        apply contDiffWithinAt_ext_coord_change
        simp [hp.2]
      have D' : DifferentiableWithinAt 𝕜 (φ'' ∘ Prod.snd) (Set.range (Prod.map I I'))
          (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
        DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0')
          differentiableWithinAt_snd (by simp [mapsTo_snd_prod])
      exact D'
    rw [DifferentiableWithinAt.fderivWithin_prod (by exact D _) (by exact D') (U _)]
    change fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _ = fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _
    rw [Set.range_prod_map] at U ⊢
    rw [fderivWithin.comp _ (by exact D0) differentiableWithinAt_fst mapsTo_fst_prod (U _),
      fderivWithin.comp _ (by exact D0) differentiableWithinAt_fst mapsTo_fst_prod (U _)]
    simp [fderivWithin_fst, U]
  · -- check that, in the fiber, the second projection is smooth in charts
    -- for this, write down a map which is obviously smooth (`C` below) and then check that the two
    -- maps coincide, up to obvious compositions.
    have C : ContMDiffAt I'.tangent (I.prod I').tangent ⊤ (fun (p : TangentBundle I' M')
        ↦ (⟨(a.1, p.1), (0, p.2)⟩ : TangentBundle (I.prod I') (M × M'))) b := by
      let f : M' → M × M' := fun m ↦ (a.1, m)
      have A : Smooth I'.tangent (I.prod I').tangent (tangentMap I' (I.prod I') f) := by
        apply Smooth.tangentMap
        exact smooth_const.prod_mk smooth_id
      have B : tangentMap I' (I.prod I') f = fun p ↦ ⟨(a.1, p.1), (0, p.2)⟩ := by
        ext p : 1
        exact tangentMap_prod_right I I'
      rw [B] at A
      exact A b
    have Z := ((contMDiffAt_totalSpace _ _).1 C).2
    simp only [modelWithCornersSelf_prod, TangentBundle.trivializationAt_apply,
      PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
      modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
      ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
      PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply] at Z
    have D1 : ContMDiff (𝓘(𝕜, E × E')) (𝓘(𝕜, E')) ⊤ (Prod.snd : E × E' → E') := by
      rw [contMDiff_iff_contDiff]; exact contDiff_snd
    have D2 : ContMDiffAt (I.tangent.prod I'.tangent) I'.tangent ⊤ Prod.snd (a, b) := smoothAt_snd
    have U' := (ContMDiffAt.comp b D1.contMDiffAt Z).comp (a, b) D2
    apply U'.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds (ModelProd (ModelProd H E) (ModelProd H' E')) (a, b)]
      with p hp
    clear U' D1 D2 C Z
    simp only [prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod_source, Set.mem_prod, TangentBundle.mem_chart_source_iff] at hp
    let φ (x : E') := I' ((chartAt H' b.proj) ((chartAt H' p.2.proj).symm (I'.symm x)))
    have D0 : DifferentiableWithinAt 𝕜 φ (Set.range I') (I' ((chartAt H' p.2.proj) p.2.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp [hp.2]
    have D (w : TangentBundle I M) :
        DifferentiableWithinAt 𝕜 (φ ∘ (Prod.snd : E × E' → E')) (Set.range (Prod.map ↑I ↑I'))
        (I ((chartAt H w.proj) w.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0)
        differentiableWithinAt_snd (by simp [mapsTo_snd_prod])
    let φ' (x : E) := I ((chartAt H a.proj) ((chartAt H a.proj).symm (I.symm x)))
    have D0' : DifferentiableWithinAt 𝕜 φ' (Set.range I)
        (I ((chartAt H a.proj) a.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp
    have D' : DifferentiableWithinAt 𝕜 (φ' ∘ Prod.fst) (Set.range (Prod.map I I'))
        (I ((chartAt H a.proj) a.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0') differentiableWithinAt_fst
        (by simp [mapsTo_fst_prod])
    have U w : UniqueDiffWithinAt 𝕜 (Set.range (Prod.map I I'))
        (I w, I' ((chartAt H' p.2.proj) p.2.proj)) := by
      simp only [Set.range_prod_map]
      apply UniqueDiffWithinAt.prod
      · exact ModelWithCorners.uniqueDiffWithinAt_image I
      · exact ModelWithCorners.uniqueDiffWithinAt_image I'
    simp only [Set.range_prod_map, ContinuousLinearMap.prod_apply, comp_def, comp_apply]
    rw [DifferentiableWithinAt.fderivWithin_prod ?_ (by exact D _) (U _)]; swap
    · let φ'' (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
      have D0' : DifferentiableWithinAt 𝕜 φ'' (Set.range I)
          (I ((chartAt H p.1.proj) p.1.proj)) := by
        apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
        apply contDiffWithinAt_ext_coord_change
        simp [hp.1]
      have D' : DifferentiableWithinAt 𝕜 (φ'' ∘ Prod.fst) (Set.range (Prod.map I I'))
          (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
        DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0')
          differentiableWithinAt_fst (by simp [mapsTo_fst_prod])
      exact D'
    rw [DifferentiableWithinAt.fderivWithin_prod (by exact D') (by exact D a) (U _)]
    change fderivWithin 𝕜 (φ ∘ Prod.snd) _ _ _ = fderivWithin 𝕜 (φ ∘ Prod.snd) _ _ _
    rw [Set.range_prod_map] at U ⊢
    rw [fderivWithin.comp _ (by exact D0) differentiableWithinAt_snd mapsTo_snd_prod (U _),
      fderivWithin.comp _ (by exact D0) differentiableWithinAt_snd mapsTo_snd_prod (U _)]
    simp [fderivWithin_snd, U]

end EquivTangentBundleProd

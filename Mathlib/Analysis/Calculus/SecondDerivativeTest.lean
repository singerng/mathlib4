/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.FirstDerivativeTest
/-!
# The Second-Derivative Test

We prove the Second-Derivative test from calculus using the First-Derivative test.
Source: [Wikipedia](https://en.wikipedia.org/wiki/Derivative_test#Proof_of_the_second-derivative_test).

## Main results

* `isLocalMin_of_deriv_deriv_pos`: The second-derivative test.

## Tags

derivative test, calculus
-/

open Set Filter Topology



/-- If `f''(x) > 0` then `f' > 0` on an interval to the right of `x`. -/
lemma deriv_pos_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ} (hf : deriv (deriv f) x₀ > 0)
    (hd : deriv f x₀ = 0) :
    ∃ u, x₀ < u ∧ ∀ b, b ∈ Ioo x₀ u → deriv f b > 0 := by
    have hD' : DifferentiableAt ℝ (deriv f) x₀ := by
        have :deriv (deriv f) x₀ ≠ 0 := by linarith
        exact differentiableAt_of_deriv_ne_zero this
    have h₀ := (@hasDerivAt_deriv_iff ℝ _ ℝ _ _ (deriv f) x₀).mpr (hD')
    have h₁ := hasDerivAt_iff_tendsto_slope.mp h₀
    rw [tendsto_nhds] at h₁

    have j₁: slope (deriv f) x₀ ⁻¹' Ioi 0 ∈ 𝓝[>] x₀ :=
      nhds_right'_le_nhds_ne x₀ <|h₁ (Set.Ioi 0) isOpen_Ioi hf
    obtain ⟨u,hu⟩ := (@mem_nhdsWithin_Ioi_iff_exists_mem_Ioc_Ioo_subset ℝ _ _ _ x₀
      (x₀ + 1) (slope (deriv f) x₀ ⁻¹' Ioi 0) (by simp)).mp j₁
    unfold slope at hu
    rw [hd] at hu
    have G₀ : ∀ b, b ∈ Ioo x₀ u → deriv f b > 0 := by
      intro b hb
      have := hu.2 hb
      simp at this
      have q₀ : b - x₀ > 0 := by aesop
      aesop
    use u
    simp at hu
    tauto

/-- Added to Mathlib by Yael Dilles. -/
lemma neg_of_neg_of_div_pos (a b : ℝ) (h : 0 < a/b) (h₁ : b < 0) : a < 0 := by
    contrapose h
    rw [not_lt]
    rw [not_lt] at h
    exact div_nonpos_of_nonneg_of_nonpos h (by linarith)

/-- If `f''(x) > 0` then `f' < 0` on an interval to the left of `x`. -/
lemma deriv_neg_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ} (hf : deriv (deriv f) x₀ > 0)
    (hd : deriv f x₀ = 0) :
    ∃ u, x₀ > u ∧ ∀ b, b ∈ Ioo u x₀ → deriv f b < 0 := by
    have hD' : DifferentiableAt ℝ (deriv f) x₀ := by
        have :deriv (deriv f) x₀ ≠ 0 := by linarith
        exact differentiableAt_of_deriv_ne_zero this
    have h₀ := (@hasDerivAt_deriv_iff ℝ _ ℝ _ _ (deriv f) x₀).mpr (hD')
    have h₁ := hasDerivAt_iff_tendsto_slope.mp h₀
    rw [tendsto_nhds] at h₁
    have := h₁ (Set.Ioi 0) isOpen_Ioi hf

    have j₀: slope (deriv f) x₀ ⁻¹' Ioi 0 ∈ 𝓝[<] x₀ :=
      nhds_left'_le_nhds_ne x₀ this
    obtain ⟨u,hu⟩ := (@mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset ℝ _ _ _ x₀
      (x₀ - 1) (slope (deriv f) x₀ ⁻¹' Ioi 0) (by simp)).mp j₀
    unfold slope at hu
    rw [hd] at hu
    have G₁ : ∀ b, b ∈ Ioo u x₀ → deriv f b < 0 := by
      intro b hb
      have hub := hu.2 hb
      simp at hub
      have q₀ : b - x₀ < 0 := by aesop
      field_simp at hub
      apply neg_of_neg_of_div_pos
      exact hub
      exact q₀
    use u
    simp at hu
    tauto

/-- If `f''(x) > 0` then `f'` changes sign at `x`. -/
lemma deriv_neg_pos_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ}
    (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0) :
    ∃ ε, ε > 0 ∧ (∀ b, b ∈ Ioo (x₀-ε) x₀ → deriv f b < 0) ∧
        ∀ b, b ∈ Ioo x₀ (x₀ + ε) → 0 < deriv f b := by
  obtain ⟨u₀,hu₀⟩ := deriv_pos_of_deriv_deriv_pos hf hd
  obtain ⟨u₁,hu₁⟩ := deriv_neg_of_deriv_deriv_pos hf hd
  use (1/2) * min (u₀ - x₀) (x₀ - u₁)
  constructor
  · aesop
  · constructor
    · intro b hb
      apply hu₁.2
      simp_all
      refine lt_trans ?_ hb.1
      have :  u₁ < x₀ - 2⁻¹ * (x₀ - u₁) := by
        have : u₁ = x₀ - (x₀ - u₁) := by ring_nf
        nth_rewrite 1 [this]
        suffices x₀ - u₁ > 2⁻¹ * (x₀ - u₁) by
            exact sub_lt_sub_left this x₀
        show x₀ - u₁ > 2⁻¹ * (x₀ - u₁)
        refine (inv_mul_lt_iff₀ ?hc).mpr <|lt_two_mul_self <|sub_pos.mpr hu₁.1
        exact zero_lt_two
      have T₀ : 2⁻¹ * min (u₀ - x₀) (x₀ - u₁) ≤ 2⁻¹ * (x₀ - u₁) := by
        refine (inv_mul_le_iff₀ ?hc).mpr ?_
        simp
      calc _ < _ := this
           _ ≤ _ := tsub_le_tsub_left T₀ x₀
    · intro b hb
      apply hu₀.2
      simp_all only [gt_iff_lt, mem_Ioo, and_imp, one_div, true_and]
      refine lt_trans hb.2 ?_
      calc _ ≤ x₀ + 2⁻¹ * (u₀ - x₀) := by simp
      _ < _ := by
        suffices 2 * (x₀ + 2⁻¹ * (u₀ - x₀)) < 2 * u₀ by
            linarith
        rw [mul_add, ← mul_assoc]
        simp
        linarith

/-- The Second-Derivative Test from calculus. -/
theorem isLocalMin_of_deriv_deriv_pos {f : ℝ → ℝ}  {x₀ : ℝ}
    (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀ := by
 obtain ⟨ε,hε⟩ := deriv_neg_pos_of_deriv_deriv_pos hf hd
 have hD' : ∀ᶠ x in 𝓝[≠] x₀, DifferentiableAt ℝ f x := by
    use Ioo (x₀-ε) (x₀+ε) ∪ {x| DifferentiableAt ℝ f x}
    constructor
    ·   refine mem_interior_iff_mem_nhds.mp ?_;
        refine mem_interior.mpr ?_
        use Ioo (x₀ - ε) (x₀ + ε)
        simp only [subset_union_left, mem_Ioo, sub_lt_self_iff, lt_add_iff_pos_right, and_self,
            true_and]
        constructor
        exact isOpen_Ioo
        tauto
    by_cases H : DifferentiableAt ℝ f x₀
    use Set.univ
    simp only [univ_mem, inter_univ, true_and]
    ext z
    constructor
    intro h
    simp only [mem_union, mem_Ioo, mem_setOf_eq]
    right
    simp_all only [gt_iff_lt, mem_Ioo, and_imp, mem_setOf_eq]
    intro h
    apply h.elim
    intro h
    by_cases H' : z < x₀
    · apply differentiableAt_of_deriv_ne_zero
      apply ne_of_lt
      apply hε.2.1
      simp_all
    · by_cases G : z = x₀
      · subst G
        simp_all
      · have : x₀ < z := by
          simp only [not_lt] at H'
          exact lt_of_le_of_ne H' fun a ↦ G (a.symm)
        apply differentiableAt_of_deriv_ne_zero
        apply ne_of_gt
        apply hε.2.2
        simp_all
    · tauto
    use {x₀}ᶜ
    simp only [mem_principal, subset_refl, true_and]
    ext z
    constructor
    intro h
    constructor
    · tauto
    · simp_all only [gt_iff_lt, mem_Ioo, and_imp, mem_setOf_eq, mem_compl_iff, mem_singleton_iff]
      intro hc
      subst hc
      tauto
    intro h
    apply h.1.elim
    intro h'
    by_cases H' : z < x₀
    · simp only [mem_setOf_eq]
      apply differentiableAt_of_deriv_ne_zero
      apply ne_of_lt
      apply hε.2.1
      simp_all
    · have : x₀ < z := by
        simp at h
        simp only [not_lt] at H'
        exact lt_of_le_of_ne H' fun a ↦ h.2 (id (Eq.symm a))
      apply differentiableAt_of_deriv_ne_zero
      apply ne_of_gt
      apply hε.2.2
      simp_all
    tauto

 obtain ⟨p,hp⟩ := hD'
 have hm₀ := mem_nhds_iff_exists_Ioo_subset.mp hp.1
 obtain ⟨l,u,hlu⟩ := hm₀
 let δ := min (x₀ - l) (u - x₀)
 let ζ := (1/2) * min δ ε
 apply isLocalMin_of_deriv_Ioo
 · show x₀ - ζ < x₀
   have : ζ > 0 := by aesop
   linarith
 · show x₀ < x₀ + ζ
   aesop
 · exact hc

 · obtain ⟨b,hb⟩ := hp.2
   simp only [mem_principal] at hb
   intro x hx
   apply DifferentiableAt.differentiableWithinAt
   suffices x ∈ p ∩ b by
    rw [← hb.2] at this
    exact this
   constructor
   ·    apply hlu.2
        simp_all only [gt_iff_lt, mem_Ioo, and_imp, mem_principal]
        constructor
        ·   refine lt_trans ?_ hx.1
            have : min (x₀ - l) (u - x₀) ≤ (x₀ - l) := by apply min_le_left
            have : min δ ε ≤ δ := min_le_left δ ε
            show l < x₀ - (1/2) * min δ ε
            linarith
        · linarith
   · apply hb.1
     simp only [mem_Ioo] at hx
     simp only [mem_compl_iff, mem_singleton_iff]
     linarith
 · obtain ⟨b,hb⟩ := hp.2
   simp only [mem_principal] at hb
   intro x hx
   apply DifferentiableAt.differentiableWithinAt
   suffices x ∈ p ∩ b by
    rw [← hb.2] at this
    exact this
   constructor
   ·    apply hlu.2
        simp_all only [gt_iff_lt, mem_Ioo, and_imp, mem_principal]
        constructor
        · linarith
        ·   refine lt_trans hx.2 ?_
            show x₀ + (1/2) * min δ ε < u
            suffices x₀ + (1/2) * δ < u by
                have : min δ ε ≤ δ := min_le_left δ ε
                linarith
            show x₀ + (1/2) * min (x₀ - l) (u - x₀) < u
            have : min (x₀ - l) (u - x₀) ≤ (u - x₀) := by apply min_le_right
            linarith
   · apply hb.1
     simp only [mem_Ioo] at hx
     simp only [mem_compl_iff, mem_singleton_iff]
     linarith
 · intro x hx
   apply le_of_lt
   have : x ∈ Ioo (x₀ - ε) x₀ := by
    simp_all only [gt_iff_lt, mem_Ioo, and_imp, mem_principal, and_true]
    have : x₀ - ε ≤ x₀ - ζ := by
        show x₀ - ε ≤ x₀ - (1/2) * min δ ε
        suffices x₀ ≤ x₀ + (1/2) * (ε - min δ ε) by
            linarith
        aesop
    linarith
   aesop
 · intro x hx
   apply le_of_lt
   have : x ∈ Ioo x₀ (x₀ + ε) := by
    simp_all only [gt_iff_lt, mem_Ioo, and_imp, mem_principal, true_and]
    have : x₀ - ε ≤ x₀ - ζ := by
        show x₀ - ε ≤ x₀ - (1/2) * min δ ε
        suffices x₀ ≤ x₀ + (1/2) * (ε - min δ ε) by linarith
        aesop
    linarith
   apply hε.2.2
   exact this

/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable


/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove different versions of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for compact spaces, from which the statements about linear functionals
on bounded continuous functions or compactly supported functions on locally compact spaces follow.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open scoped Classical BoundedContinuousFunction ENNReal
open Set Function TopologicalSpace CompactlySupported MeasureTheory NNReal

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

/-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
`λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
  sInf (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })

section Λ_mono

variable [T2Space X] [LocallyCompactSpace X]


-- I tried to generalize `Function.support_sub`. It turns out that `Sub` in general does not have
-- `sub_self`. so I decided to prove directly this.
lemma Λ_mono (f₁ f₂ : C_c(X, ℝ≥0)) (h : f₁.1 ≤ f₂.1) : Λ f₁ ≤ Λ f₂ := by
  have ex_diff : ∃ (g : C_c(X, ℝ≥0)), f₁ + g = f₂ := by
    set g_cf := f₂.1 - f₁.1 with hg_cf
    have g_cp : HasCompactSupport g_cf := by
      apply IsCompact.of_isClosed_subset
        (IsCompact.union f₁.hasCompactSupport' f₂.hasCompactSupport') isClosed_closure
      rw [tsupport, tsupport, ← closure_union]
      apply closure_mono
      intro x
      simp only [mem_support, ne_eq, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap, mem_union]
      rw [hg_cf]
      simp only [ContinuousMap.sub_apply, CompactlySupportedContinuousMap.coe_toContinuousMap]
      by_contra!
      rw [this.2.1, this.2.2] at this
      simp only [tsub_self, ne_eq, not_true_eq_false, and_self, and_true] at this
    use ⟨g_cf, g_cp⟩
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mk,
      Pi.add_apply]
    rw [NNReal.coe_inj, hg_cf]
    simp only [ContinuousMap.sub_apply, CompactlySupportedContinuousMap.coe_toContinuousMap]
    exact add_tsub_cancel_of_le (h x)
  obtain ⟨g, hg⟩ := ex_diff
  rw [← hg]
  simp only [map_add, le_add_iff_nonneg_right, zero_le]



end Λ_mono

section RieszMonotone

variable [T2Space X] [LocallyCompactSpace X]

/-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
functions f on X such that `f ≥ 1` on K. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    exact closure_mono interior_subset
  obtain ⟨f, hsuppfsubV, hfeq1onK, hfinicc⟩ :=
    exists_tsupport_one_of_isOpen_isClosed isOpen_interior hIsCompact_closure_interior
      (IsCompact.isClosed K.2) hKsubintV
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hVcp (isClosed_tsupport f)
      (Set.Subset.trans hsuppfsubV interior_subset)
  use nnrealPartCompactlySupported ⟨f, hfHasCompactSupport⟩
  intro x hx
  apply le_of_eq
  simp only [nnrealPartCompactlySupported_apply, CompactlySupportedContinuousMap.coe_mk]
  rw [← Real.toNNReal_one]
  rw [Real.toNNReal_eq_toNNReal_iff (zero_le_one' ℝ) (hfinicc x).1]
  exact (EqOn.symm hfeq1onK) hx

/-- Riesz content λ (associated with a positive linear functional Λ) is
monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ :=
  csInf_le_csInf (OrderBot.bddBelow _) (rieszContentAux_image_nonempty Λ K₂)
    (image_subset Λ (setOf_subset_setOf.mpr fun _ f_hyp x x_in_K₁ => f_hyp x (h x_in_K₁)))

end RieszMonotone

section RieszSubadditive

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ≥0)} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
    rieszContentAux Λ K ≤ Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

variable [T2Space X] [LocallyCompactSpace X]

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ f : C_c(X, ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

/-- The Riesz content λ associated to a given positive linear functional Λ is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
    rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive


section PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

lemma exists_sum_one_of_isCompact_nnreal
    {s : Fin 2 → Set X} {t : Set X} (s_compact : ∀ i, IsCompact (s i))
    (t_compact : IsCompact t) (disj : Disjoint (s 0) (s 1)) (hst : ⋃ i, s i ⊆ t) :
    ∃ (f₀ f₁ : C_c(X, ℝ≥0)), EqOn f₀ 1 (s 0) ∧ EqOn f₁ 1 (s 1) ∧ EqOn (f₀ + f₁) 1 t := by
  set so : Fin 2 → Set X := fun j => if j = 0 then (s 0)ᶜ else (s 1)ᶜ with hso
  have soopen : ∀ j, IsOpen (so j) := by
    intro j
    by_cases h0 : j = 0
    · rw [h0, hso]
      simp only [Fin.isValue, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s_compact 0
    · rw [hso]
      simp only [Fin.isValue]
      rw [if_neg h0]
      simp only [Fin.isValue, isOpen_compl_iff]
      exact IsCompact.isClosed <| s_compact 1
  have hsot : t ⊆ ⋃ j, so j := by
    rw [hso]
    simp only [Fin.isValue]
    intro x hx
    rw [mem_iUnion]
    rw [← subset_compl_iff_disjoint_right, ← compl_compl (s 0), compl_subset_iff_union] at disj
    have h : x ∈ (s 0)ᶜ ∨ x ∈ (s 1)ᶜ := by
      rw [← mem_union, disj]
      trivial
    apply Or.elim h
    · intro h0
      use 0
      simp only [Fin.isValue, ↓reduceIte]
      exact h0
    · intro h1
      use 1
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      exact h1
  obtain ⟨f, f_supp_in_so, sum_f_one_on_t, f_in_icc, f_hcs⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact soopen t_compact hsot
  use (nnrealPartCompactlySupported (⟨f 1, f_hcs 1⟩ : C_c(X, ℝ))),
    (nnrealPartCompactlySupported (⟨f 0, f_hcs 0⟩ : C_c(X, ℝ)))
  simp only [Fin.isValue, CompactlySupportedContinuousMap.coe_add]
  have sum_one_x : ∀ x, x ∈ t → (f 0) x + (f 1) x = 1 := by
    intro x hx
    let sum_one := sum_f_one_on_t hx
    simp only [Finset.sum_apply, Fin.sum_univ_two, Fin.isValue, Pi.one_apply] at sum_one
    exact sum_one
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Fin.isValue, nnrealPartCompactlySupported_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 0) x = 0 := by
      rw [← nmem_support]
      have : s 0 ⊆ (tsupport (f 0))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 0))
        rw [hso]
        simp only [Fin.isValue, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [iUnion_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem (hst 0) hx), this]
    exact Eq.symm (AddZeroClass.zero_add ((f 1) x))
  · intro x hx
    simp only [Fin.isValue, nnrealPartCompactlySupported_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 1) x = 0 := by
      rw [← nmem_support]
      have : s 1 ⊆ (tsupport (f 1))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 1))
        rw [hso]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [iUnion_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem (hst 1) hx), this]
    exact Eq.symm (AddMonoid.add_zero ((f 0) x))
  · intro x hx
    simp only [Fin.isValue, Pi.add_apply, nnrealPartCompactlySupported_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply]
    rw [Real.toNNReal_add_toNNReal (f_in_icc 1 x).1 (f_in_icc 0 x).1, add_comm]
    simp only [Fin.isValue, Real.toNNReal_eq_one]
    exact sum_one_x x hx

end PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

lemma rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X}
    (disj : Disjoint (K₁ : Set X) K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  set K : Fin 2 → Set X := fun j => if j = 0 then K₁ else K₂ with hK
  have K_compact : ∀ j, IsCompact (K j) := by
    intro j
    by_cases h0 : j = 0
    · rw [hK, h0]
      simp only [Fin.isValue, ↓reduceIte]
      exact Compacts.isCompact K₁
    · rw [hK]
      simp only [Fin.isValue, apply_dite]
      rw [if_neg h0]
      exact Compacts.isCompact K₂
  have hsuppf : ∀ x ∈ K₁ ⊔ K₂, x ∈ support f := by
    intro x hx
    rw [mem_support]
    exact Ne.symm (ne_of_lt <| lt_of_lt_of_le (zero_lt_one' ℝ≥0) (hf x hx))
  have hsubsuppf : (K₁ : Set X) ∪ (K₂ : Set X) ⊆ tsupport f := subset_trans hsuppf subset_closure
  have hKt : ⋃ j, K j ⊆ tsupport f := by
    apply iUnion_subset
    intro j
    by_cases h0 : j = 0
    · rw [h0, hK]
      simp only [Fin.isValue, ↓reduceIte]
      exact (union_subset_iff.mp hsubsuppf).1
    · rw [hK]
      simp only [Fin.isValue]
      rw [if_neg h0]
      exact (union_subset_iff.mp hsubsuppf).2
  obtain ⟨g₁, g₂, hg₁, hg₂, sum_g⟩ := exists_sum_one_of_isCompact_nnreal K_compact
    f.hasCompactSupport'.isCompact disj hKt
  have f_eq_sum : f = g₁ * f + g₂ * f := by
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mul,
      Pi.add_apply, Pi.mul_apply, NNReal.coe_add, NNReal.coe_mul,
      Eq.symm (RightDistribClass.right_distrib _ _ _), ← NNReal.coe_add, ← Pi.add_apply]
    by_cases h : f x = 0
    · rw [h]
      simp only [NNReal.coe_zero, NNReal.coe_add, mul_zero]
    · push_neg at h
      simp only [CompactlySupportedContinuousMap.coe_add, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap] at sum_g
      rw [sum_g (mem_of_subset_of_mem subset_closure (mem_support.mpr h))]
      simp only [Pi.one_apply, NNReal.coe_one, one_mul]
  rw [← Λf_eq_b, f_eq_sum, map_add]
  have aux₁ : ∀ x ∈ K₁, 1 ≤ (g₁ * f) x := by
    intro x x_in_K₁
    simp [hg₁ x_in_K₁, hf x (mem_union_left _ x_in_K₁)]
  have aux₂ : ∀ x ∈ K₂, 1 ≤ (g₂ * f) x := by
    intro x x_in_K₂
    simp [hg₂ x_in_K₂, hf x (mem_union_right _ x_in_K₂)]
  exact add_le_add (rieszContentAux_le Λ aux₁) (rieszContentAux_le Λ aux₂)

/-- The contents induced by the linear functional `Λ`. -/
noncomputable def rieszContent (Λ : (C_c(X, ℝ≥0)) →ₗ[ℝ≥0] ℝ≥0) : Content X where
  toFun := rieszContentAux Λ
  mono' := fun _ _ ↦ rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ ↦ rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

lemma rieszContent_neq_top {K : Compacts X} : rieszContent Λ K ≠ ⊤ := by
  simp only [ne_eq, ENNReal.coe_ne_top, not_false_eq_true]

lemma Real.le_of_forall_lt_one_lt_mul (a b : ℝ) (hb : 0 ≤ b) :
    (∀ (ε : ℝ), 1 < ε → a ≤  b * ε) → a ≤ b := by
  intro h
  by_cases hbzero : b = 0
  · rw [hbzero]
    rw [← zero_mul 2, ← hbzero]
    exact h 2 one_lt_two
  · apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    push_neg at hbzero
    have bpos : 0 < b := by
      exact lt_of_le_of_ne hb (id (Ne.symm hbzero))
    have bdiv : 1 < (b + ε) / b := by
      apply (one_lt_div bpos).mpr
      exact lt_add_of_pos_right b hε
    have : a ≤ b * ((b + ε) / b) := h ((b + ε) / b) bdiv
    rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt bpos), mul_one] at this
    exact this

lemma rieszContentRegular : (rieszContent Λ).ContentRegular := by
  intro K
  rw [rieszContent]
  simp only
  apply le_antisymm
  · apply le_iInf
    simp only [le_iInf_iff, ENNReal.coe_le_coe]
    intro K' hK'
    exact rieszContentAux_mono Λ (Set.Subset.trans hK' interior_subset)
  · rw [iInf_le_iff]
    intro b hb
    rw [rieszContentAux, ENNReal.le_coe_iff]
    have : b < ⊤ := by
      obtain ⟨F, hF⟩ := exists_compact_superset K.2
      exact lt_of_le_of_lt (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2) ENNReal.coe_lt_top
    use b.toNNReal
    refine ⟨Eq.symm (ENNReal.coe_toNNReal (ne_of_lt this)), ?_⟩
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_le_coe]
    rw [← NNReal.coe_le_coe]
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    set εnn : ℝ≥0 := ⟨ε, le_of_lt hε⟩ with hεnn
    have εnneq : ε.toNNReal = εnn := Real.toNNReal_of_nonneg (le_of_lt hε)
    rw [← coe_mk ε (le_of_lt hε), ← NNReal.coe_add, coe_le_coe]
    obtain ⟨f, hfleoneonK, hfle⟩ := exists_lt_rieszContentAux_add_pos Λ K (Real.toNNReal_pos.mpr hε)
    rw [rieszContentAux, εnneq] at hfle
    rw [← Real.toNNReal_pos] at hε
    apply le_of_lt (lt_of_le_of_lt _ hfle)
    have : 0 ≤ f.1 := by
      intro x
      simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
        CompactlySupportedContinuousMap.coe_toContinuousMap]
      exact zero_le (f x)
    apply Real.le_of_forall_lt_one_lt_mul
    · simp only [val_eq_coe, zero_le_coe]
    · intro α hα
      simp only
      have : (Λ f).val * α = Λ (α.toNNReal • f) := by
        simp only [val_eq_coe, map_smul, smul_eq_mul, NNReal.coe_mul, Real.coe_toNNReal']
        rw [max_eq_left <| le_of_lt (lt_of_le_of_lt zero_le_one hα)]
        exact mul_comm _ _
      rw [this]
      set K' := f ⁻¹' (Ici α⁻¹.toNNReal) with hK'
      have hKK' : K.carrier ⊆ interior K' := by
        rw [subset_interior_iff]
        use f ⁻¹' (Ioi α⁻¹.toNNReal)
        refine ⟨?_, ?_, ?_⟩
        · apply IsOpen.preimage f.1.2
          exact isOpen_Ioi
        · intro x hx
          rw [Set.mem_preimage, Set.mem_Ioi]
          exact lt_of_lt_of_le (Real.toNNReal_lt_one.mpr (inv_lt_one_of_one_lt₀ hα))
            (hfleoneonK x hx)
        · rw [hK']
          intro x hx
          simp only [mem_preimage, mem_Ioi] at hx
          simp only [mem_preimage, mem_Ici]
          exact le_of_lt hx
      have hK'cp : IsCompact K' := by
        apply IsCompact.of_isClosed_subset f.2
        · simp only [smul_eq_mul] at hK'
          exact IsClosed.preimage f.1.2 isClosed_Ici
        · rw [hK']
          apply Set.Subset.trans _ subset_closure
          intro x hx
          simp only [mem_preimage, mem_Ici] at hx
          simp only [mem_support]
          apply ne_of_gt
          rw [Real.toNNReal_inv] at hx
          exact (lt_of_lt_of_le
            (inv_pos_of_pos (lt_trans zero_lt_one (Real.one_lt_toNNReal.mpr hα))) hx)
      set hb' := hb ⟨K', hK'cp⟩
      simp only [Compacts.coe_mk, le_iInf_iff] at hb'
      have hbK' : b ≤ rieszContent Λ ⟨K', hK'cp⟩ := hb' hKK'
      rw [ENNReal.le_coe_iff] at hbK'
      obtain ⟨p, hp⟩ := hbK'
      rw [hp.1]
      simp only [ENNReal.toNNReal_coe, val_eq_coe, map_smul, smul_eq_mul, NNReal.coe_mul,
        Real.coe_toNNReal', ge_iff_le]
      apply le_trans (NNReal.GCongr.toReal_le_toReal hp.2)
      rw [rieszContent]
      simp only
      rw [rieszContentAux, ← Real.coe_toNNReal (α ⊔ 0) (le_max_right α 0), ← NNReal.coe_mul,
        NNReal.coe_le_coe]
      apply csInf_le
      · simp only [OrderBot.bddBelow]
      · rw [mem_image]
        simp only [mem_setOf_eq]
        use α.toNNReal • f
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
          rw [← NNReal.coe_le_coe]
          simp only [coe_one, NNReal.coe_mul, Real.coe_toNNReal']
          rw [← (left_eq_sup.mpr <| le_of_lt (lt_of_le_of_lt zero_le_one hα)), mul_comm]
          apply (inv_le_iff_one_le_mul₀ (lt_trans zero_lt_one hα)).mp
          rw [← Set.mem_Ici]
          have hxK' : x ∈ K' := by exact hx
          rw [hK'] at hxK'
          simp only [mem_preimage, mem_Ici] at hxK'
          simp only [mem_Ici, ge_iff_le]
          exact Real.toNNReal_le_iff_le_coe.mp hx
        · simp only [map_smul, smul_eq_mul, mul_eq_mul_right_iff]
          left
          rw [Real.toNNReal_eq_toNNReal_iff (le_of_lt (lt_of_le_of_lt zero_le_one hα))
            (le_max_right α 0), left_eq_sup]
          exact le_of_lt (lt_of_le_of_lt zero_le_one hα)

variable [MeasurableSpace X] [BorelSpace X]

theorem MeasureTheory.integral_tsupport {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {F : X → M} {ν : MeasureTheory.Measure X} :
    ∫ (x : X), F x ∂ν = ∫ (x : X) in tsupport F, F x ∂ν := by
  rw [← MeasureTheory.setIntegral_univ]
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
    (subset_univ _)
  intro x hx
  apply image_eq_zero_of_nmem_tsupport
  exact not_mem_of_mem_diff hx

@[to_additive]
theorem le_iff_forall_one_lt_le_mul' {α : Type*} [LinearOrder α] [DenselyOrdered α] [Monoid α]
    [ExistsMulOfLE α] [MulLeftReflectLT α] {a b : α} [MulLeftStrictMono α] :
    a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
  ⟨fun h _ hε ↦ lt_mul_of_le_of_one_lt h hε |>.le, le_of_forall_one_lt_le_mul⟩

open NNReal

example {a b : ℝ≥0} : a ≤ b ↔ ∀ (ε : ℝ≥0), 0 < ε → a ≤ b + ε :=
  le_iff_forall_pos_le_add'

/-- `rieszContent` is promoted to a measure. -/
def μ := (MeasureTheory.Content.measure (rieszContent Λ))

lemma leRieszMeasure_isCompact {f : C_c(X, ℝ≥0)} (hf : ∀ (x : X), f x ≤ 1) {K : Compacts X}
    (h : tsupport f ⊆ K) : ENNReal.ofReal (Λ f) ≤ (μ Λ) K := by
  rw [μ]
  rw [MeasureTheory.Content.measure_eq_content_of_regular (rieszContent Λ)
    (rieszContentRegular Λ)]
  simp only
  rw [rieszContent]
  simp only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add'.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ K hε
  apply le_of_lt (lt_of_le_of_lt _ hg.2)
  apply Λ_mono Λ
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x) (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    exact zero_le (g x)

lemma leRieszMeasure_isOpen {f : C_c(X, ℝ≥0)} (hf : ∀ (x : X), f x ≤ 1) {V : Opens X}
    (h : tsupport f ⊆ V) :
    ENNReal.ofReal (Λ f) ≤ (μ Λ) V := by
  apply le_trans _ (MeasureTheory.measure_mono h)
  rw [← TopologicalSpace.Compacts.coe_mk (tsupport f) f.2]
  apply leRieszMeasure_isCompact Λ hf
  simp only [Compacts.coe_mk]
  exact subset_rfl

/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Docstring

-/

section

theorem IntervalIntegrable.congr {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E}
    {μ : MeasureTheory.Measure ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Set.uIoc a b)] g) :
    IntervalIntegrable g μ a b := by
  rwa [intervalIntegrable_iff, ← MeasureTheory.integrableOn_congr_fun_ae h,
    ← intervalIntegrable_iff]

end

noncomputable section

open Finset intervalIntegral MeasureTheory IntervalIntegrable

theorem AbelSummation (c : ℕ → ℂ) {f : ℝ → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntervalIntegrable (deriv f) volume a b) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in a..b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
   -- We prove some inequalities to be used later on by linarith / positivity
  have : ⌊a⌋₊ ≤ a := Nat.floor_le ha
  have : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one _
  have : b < ⌊b⌋₊ + 1 := Nat.lt_floor_add_one _
  -- The partial sum function is locally constant
  have h_sumlocc : ∀ (n : ℕ), ∀ᵐ t, t ∈ Set.Icc (n : ℝ) (n + 1) →
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ k ∈ Icc 0 n, c k := fun n ↦ by
    filter_upwards[Ico_ae_eq_Icc (a := (n : ℝ)) (b := n + 1)] with t h ht
    rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]
  -- Thus, we can integrate it
  have h_integ : ∀ (t₁ t₂ : ℝ) (n : ℕ) (_ : Set.uIoc t₁ t₂ ⊆ Set.Icc n (n + 1))
      (_ : Set.uIcc t₁ t₂ ⊆ Set.Icc a b),
      ∫ t in t₁..t₂, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k = (f t₂ - f t₁) * ∑ k ∈ Icc 0 n, c k := by
    intro t₁ t₂ n ht₁ ht₂
    rw [← integral_deriv_eq_sub (fun t ht ↦ hf_diff _ (ht₂ ht)) (hf_int.mono_set
      (by rwa [Set.uIcc_of_le hab])), ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [h_sumlocc n] with t h h' using by rw [h (ht₁ h')]
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul, h_integ, sub_self]
    · rw [Set.uIoc_of_le hab]
      exact Set.Ioc_subset_Icc_self.trans <|
        Set.Icc_subset_Icc (by rw [← hb]; linarith) (by linarith)
    · rw [Set.uIcc_of_le hab]
  -- Some more inequalities for linarith / positivity
  have : 1 ≤ b := Nat.floor_pos.mp (by linarith)
  have : ⌊b⌋₊ ≤ b := Nat.floor_le (by positivity)
  have : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one,  ← Nat.le_floor_iff (by positivity)]
  have : a < ⌊b⌋₊ := by rwa [← Nat.floor_lt ha]
  -- And some additional properties
  have h_Icck : ∀ ⦃k⦄, k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊ → Set.Icc (k : ℝ) (k + 1) ⊆ Set.Icc a b := by
    refine fun k hk ↦ Set.Icc_subset_Icc ?_ ?_
    · have := (Nat.succ_eq_add_one _) ▸ (Set.mem_Ico.mp hk).1
      exact le_of_lt <| (Nat.floor_lt' (by linarith)).mp this
    · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (by linarith)]
      exact (Set.mem_Ico.mp hk).2
  have h_locint : ∀ (t₁ t₂ : ℝ) (n : ℕ) (_ : Set.uIoc t₁ t₂ ⊆ Set.Icc n (n + 1))
      (_ : Set.uIcc t₁ t₂ ⊆ Set.Icc a b),
      IntervalIntegrable (fun t ↦ deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) volume t₁ t₂ := by
    refine fun t₁ t₂ n ht₁ ht₂ ↦ ((hf_int.mul_const (∑ k ∈ Icc 0 n, c k)).mono_set
      ((Set.uIcc_of_le (by linarith : a ≤ b)) ▸ ht₂)).congr ?_
    refine ae_restrict_of_ae_restrict_of_subset ht₁ <| (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [h_sumlocc n] with t ht₁ ht₂ using by rw [ht₁ ht₂]
  have h_int : IntervalIntegrable (fun t ↦ deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) volume a b := by
    refine (h_locint a (⌊a⌋₊ + 1 : ℕ) ⌊a⌋₊ ?_ ?_).trans <|
      (trans_iterate_Ico hb fun k hk ↦ h_locint k _ k ?_ ?_).trans (h_locint ⌊b⌋₊ b ⌊b⌋₊ ?_ ?_)
    · rw [Nat.cast_add_one, Set.uIoc_of_le (by linarith)]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left (by linarith))
    · rw [Nat.cast_add_one, Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc_right (by linarith)
    · rw [Set.uIoc_of_le (by simp), Nat.cast_add_one]
      exact Set.Ioc_subset_Icc_self
    · rw [Set.uIcc_of_le (by simp), Nat.cast_add_one]
      exact h_Icck hk
    · rw [Set.uIoc_of_le (by linarith)]
      exact Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc_right (by linarith)
    · rw [Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc_left (by linarith)
  -- `erw` is necessary here because of the `•` in the statement of `sum_Ioc_by_parts`
  erw [sum_Ioc_by_parts (fun k ↦ f k) _ (by linarith) hb]
  simp_rw [range_eq_Ico, Nat.Ico_succ_right, smul_eq_mul]
  rw [show ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f ↑k) * ∑ n ∈ Icc 0 k, c n =
    ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), ∫ (t : ℝ) in ↑k..↑(k + 1), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n by
      refine sum_congr rfl fun k _ ↦ (h_integ _ _ _ (by simp [Set.Ioc_subset_Icc_self]) ?_).symm
      rw [Set.uIcc_of_le (by simp), Nat.cast_add_one]
      refine h_Icck ?_
      rwa [← Nat.sub_add_cancel (by linarith : 1 ≤ ⌊b⌋₊), ← Finset.coe_Ico, Nat.Ico_succ_succ],
    ← Nat.Ico_succ_succ, Nat.succ_eq_add_one, Nat.succ_eq_add_one,
    tsub_add_cancel_of_le (by linarith), sum_integral_adjacent_intervals_Ico (by linarith),
    Nat.cast_add, Nat.cast_one, ← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1),
    ← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b), h_integ a (⌊a⌋₊ + 1) ⌊a⌋₊,
    h_integ ⌊b⌋₊ b ⌊b⌋₊]
  · ring
  -- Now, we just need to check all the technical conditions
  · rw [Set.uIoc_of_le (by linarith)]
    exact Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc_right (by linarith)
  · rw [Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_left (by linarith)
  · rw [Set.uIoc_of_le (by linarith)]
    exact Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc_left (by linarith)
  · rw [Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_right (by linarith)
  · refine h_int.mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_right (by linarith)
  · refine h_int.mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_left (by linarith)
  · refine h_int.mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_right (by linarith)
  · refine h_int.mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc_right (by linarith)
  · intro k hk
    refine h_int.mono_set ?_
    rw [Set.uIcc_of_le (by simp), Set.uIcc_of_le (by linarith), Nat.cast_add_one]
    exact h_Icck hk

theorem AbelSummation₀ (c : ℕ → ℂ) (f : ℝ → ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 0 b, DifferentiableAt ℝ f t)
    (hf_int : IntervalIntegrable (deriv f) volume 0 b) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in (0 : ℝ)..b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons, ← Nat.floor_zero (α := ℝ), AbelSummation c le_rfl hb hf_diff hf_int,
    Nat.floor_zero, Nat.cast_zero, Icc_self, sum_singleton]
  ring

theorem AbelSummation₁ (c : ℕ → ℂ) (hc : c 0 = 0) {f : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ f t)
    (hf_int : IntervalIntegrable (deriv f) volume 1 b) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in (1: ℝ)..b, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  obtain hb' | hb' := le_or_gt 1 b
  · have : 1 ≤ ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb'
    nth_rewrite 1 [Finset.Icc_eq_cons_Ioc (by linarith), sum_cons, ← Nat.Icc_succ_left,
      Finset.Icc_eq_cons_Ioc (by linarith), sum_cons]
    rw [Nat.succ_eq_add_one, zero_add, ← Nat.floor_one (α := ℝ), AbelSummation c zero_le_one hb'
      hf_diff hf_int, Nat.floor_one, Nat.cast_one, Finset.Icc_eq_cons_Ioc zero_le_one, sum_cons,
      show 1 = 0 + 1 by rfl, Nat.Ioc_succ_singleton, zero_add, sum_singleton, hc, mul_zero,
      zero_add]
    ring
  · rw [Nat.floor_eq_zero.mpr hb', Icc_self, sum_singleton, sum_singleton]
    
    sorry

open Filter Topology

theorem integral_repr (f : ℕ → ℂ) (s : ℂ) (hs : LSeriesSummable f s):
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 0 ⌊t⌋₊, f k) / t ^ (s + 1)) := by
  have := fun N : ℕ ↦ AbelSummation₁ (fun k ↦ if k = 0 then 0 else f k)
    (f := fun x ↦ x ^ (- s)) (b := N + 1) ?_ ?_ ?_ ?_

  have : Tendsto (fun n ↦ ∑ k in range n, LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    hs.hasSum.tendsto_sum_nat

  sorry

#exit

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ‖S f t - l * t‖ ≤ ε := sorry

theorem final_step1 (s : ℝ) (ε : ℝ) :
    ∃ c, ‖(LSeries f s) / s - l / (s - 1)‖ ≤ ε / (s - 1) + c := sorry

theorem final_step2 (ε : ℝ) (hε : 0 < ε) :
    limsup (fun s : ℝ ↦ ‖(s - 1) * LSeries f s - l‖) (𝓝[<] 1) ≤ ε := sorry

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := sorry

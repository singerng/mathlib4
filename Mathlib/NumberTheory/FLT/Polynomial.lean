/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.Polynomial.Content

/-!
# Fermat's Last Theorem for polynomials over a field

This file states and proves the Fermat's Last Theorem for polynomials over a field.
For `n ≥ 3` not divisible by the characteristic of the coefficient field `k` and (pairwise) nonzero
coprime polynomials `a, b, c` (over a field) with `a ^ n + b ^ n = c ^ n`,
all polynomials must be constants.

More generally, we can prove non-solvability of Fermat-Catalan equation: there are no
non-constant polynomial solution of the equation `u * a ^ p + v * b ^ q + w * c ^ r = 0`, where
`p, q, r ≥ 3` with `p * q + q * r + r * p ≤ p * q * r` and not divisible by `char k`
and `u, v, w` are nonzero elements in `k`.

The proof uses Mason-Stothers theorem (Polynomial ABC theorem) and infinite descent
(for characteristic p case).
-/

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

variable {k : Type _} [Field k]
variable {R : Type _} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

private lemma Ne.isUnit_C {u : k} (hu : u ≠ 0) : IsUnit (C u) :=
  Polynomial.isUnit_C.mpr hu.isUnit

-- Multiplying units preserve coprimality
private lemma isCoprime_mul_units_left {a b : k[X]} {u v : k} (hu : u ≠ 0) (hv : v ≠ 0) :
    IsCoprime (C u * a) (C v * b) ↔ IsCoprime a b :=
  Iff.trans
    (isCoprime_mul_unit_left_left hu.isUnit_C _ _)
    (isCoprime_mul_unit_left_right hv.isUnit_C _ _)

-- auxiliary lemma that 'rotates' coprimality
private lemma rot_coprime
    {p q r : ℕ} {a b c : k[X]} {u v w : k}
    {hp : 0 < p} {hq : 0 < q} {hr : 0 < r}
    {hu : u ≠ 0} {hv : v ≠ 0} {hw : w ≠ 0}
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) (hab : IsCoprime a b) : IsCoprime b c := by
  rw [← IsCoprime.pow_iff hp hq, ← isCoprime_mul_units_left hu hv] at hab
  rw [add_eq_zero_iff_neg_eq] at heq
  rw [← IsCoprime.pow_iff hq hr, ← isCoprime_mul_units_left hv hw,
    ← heq, IsCoprime.neg_right_iff]
  convert IsCoprime.add_mul_left_right hab.symm 1 using 2
  rw [mul_one]

private lemma ineq_pqr_contradiction {p q r a b c : Nat}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (hpa : p * a < a + b + c)
    (hqb : q * b < a + b + c)
    (hrc : r * c < a + b + c) : False := by
  suffices h : p * q * r * (a + b + c) + 1 ≤ p * q * r * (a + b + c) by simp at h
  calc
    _ = (p * a) * (q * r) + (q * b) * (r * p) + (r * c) * (p * q) + 1 := by ring
    _ ≤ (a + b + c) * (q * r) + (a + b + c) * (r * p) + (a + b + c) * (p * q) := by
      rw [Nat.succ_le]
      have hpq := Nat.mul_pos hp hq
      have hqr := Nat.mul_pos hq hr
      have hrp := Nat.mul_pos hr hp
      refine (Nat.add_lt_add (Nat.add_lt_add ?_ ?_) ?_)
        <;> apply (Nat.mul_lt_mul_right ?_).mpr
        <;> assumption
    _ = (q * r + r * p + p * q) * (a + b + c) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hineq

private lemma derivative_pow_eq_zero_iff {n : ℕ} (chn : ¬ringChar k ∣ n) {a : k[X]}  :
    derivative (a ^ n) = 0 ↔ derivative a = 0 := by
  constructor
  · intro apd
    rw [derivative_pow, C_eq_natCast, mul_eq_zero, mul_eq_zero] at apd
    rcases apd with (nz | powz) | goal
    · rw [← C_eq_natCast, C_eq_zero] at nz
      exact (chn (ringChar.dvd nz)).elim
    · have az : a = 0 := pow_eq_zero powz
      rw [az, map_zero]
    · exact goal
  · intro hd
    rw [derivative_pow, hd, MulZeroClass.mul_zero]

private lemma mul_eq_zero_left_iff
    {M₀ : Type*} [MulZeroClass M₀] [NoZeroDivisors M₀]
    {a : M₀} {b : M₀}  (ha : a ≠ 0) : a * b = 0 ↔ b = 0 := by
  rw [mul_eq_zero]
  tauto

private lemma radical_natDegree_le [DecidableEq k] {a : k[X]} (h : a ≠ 0) :
    (radical a).natDegree ≤ a.natDegree :=
  natDegree_le_of_dvd (radical_dvd_self a) h

private theorem Polynomial.flt_catalan_deriv [DecidableEq k]
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q) (chr : ¬ringChar k ∣ r)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  have hbc : IsCoprime b c := by apply rot_coprime heq <;> assumption
  have hca : IsCoprime c a := by
    rw [add_rotate] at heq; apply rot_coprime heq <;> assumption
  have hCu := C_ne_zero.mpr hu
  have hCv := C_ne_zero.mpr hv
  have hCw := C_ne_zero.mpr hw
  have hap := pow_ne_zero p ha
  have hbq := pow_ne_zero q hb
  have hcr := pow_ne_zero r hc
  have habp : IsCoprime (C u * a ^ p) (C v * b ^ q) :=
    (isCoprime_mul_units_left hu hv).mpr hab.pow
  have hbcp : IsCoprime (C v * b ^ q) (C w * c ^ r) :=
    (isCoprime_mul_units_left hv hw).mpr hbc.pow
  have hcap : IsCoprime (C w * c ^ r) (C u * a ^ p) :=
    (isCoprime_mul_units_left hw hu).mpr hca.pow
  have habcp := hcap.symm.mul_left hbcp

  -- Use Mason-Stothers theorem
  rcases Polynomial.abc
      (mul_ne_zero hCu hap) (mul_ne_zero hCv hbq) (mul_ne_zero hCw hcr)
      habp heq with nd_lt | dr0
  · simp_rw [radical_mul habcp, radical_mul habp,
        radical_isUnit_mul_left hu.isUnit_C,
        radical_isUnit_mul_left hv.isUnit_C,
        radical_isUnit_mul_left hw.isUnit_C,
        radical_pow a hp, radical_pow b hq, radical_pow c hr,
        natDegree_mul hCu hap,
        natDegree_mul hCv hbq,
        natDegree_mul hCw hcr,
        natDegree_C, natDegree_pow, zero_add,
        ← radical_mul hab,
        ← radical_mul (hca.symm.mul_left hbc)] at nd_lt

    rcases nd_lt with ⟨hpa', hqb', hrc'⟩
    have habc := mul_ne_zero (mul_ne_zero ha hb) hc
    have hpa := hpa'.trans (radical_natDegree_le habc)
    have hqb := hqb'.trans (radical_natDegree_le habc)
    have hrc := hrc'.trans (radical_natDegree_le habc)
    rw [natDegree_mul (mul_ne_zero ha hb) hc,
        natDegree_mul ha hb, Nat.add_one_le_iff] at hpa hqb hrc

    exfalso
    exact (ineq_pqr_contradiction hp hq hr hineq hpa hqb hrc)
  · rw [derivative_C_mul, derivative_C_mul, derivative_C_mul,
        mul_eq_zero_left_iff (C_ne_zero.mpr hu),
        mul_eq_zero_left_iff (C_ne_zero.mpr hv),
        mul_eq_zero_left_iff (C_ne_zero.mpr hw),
        derivative_pow_eq_zero_iff chp,
        derivative_pow_eq_zero_iff chq,
        derivative_pow_eq_zero_iff chr] at dr0
    exact dr0

-- helper lemma that gives a baggage of small facts on `contract (ringChar k) a`
private lemma find_contract {a : k[X]}
    (ha : a ≠ 0) (hda : derivative a = 0) (chn0 : ringChar k ≠ 0) :
    ∃ ca, ca ≠ 0 ∧
      a = expand k (ringChar k) ca ∧
      a.natDegree = ca.natDegree * ringChar k := by
  have heq := (expand_contract (ringChar k) hda chn0).symm
  refine ⟨contract (ringChar k) a, ?_, heq, ?_⟩
  · intro h
    rw [h, map_zero] at heq
    exact ha heq
  · rw [← natDegree_expand, ← heq]

private theorem expand_dvd {a b : k[X]} (n : ℕ) (h : a ∣ b) :
    expand k n a ∣ expand k n b := by
  rcases h with ⟨t, eqn⟩
  use expand k n t
  rw [eqn, map_mul]

variable [DecidableEq k]

private theorem is_coprime_of_expand
    {a b : k[X]} {n : ℕ} (hn : n ≠ 0) :
    IsCoprime (expand k n a) (expand k n b) → IsCoprime a b := by
  simp_rw [← EuclideanDomain.gcd_isUnit_iff]
  cases' EuclideanDomain.gcd_dvd a b with ha hb
  have he := EuclideanDomain.dvd_gcd (expand_dvd n ha) (expand_dvd n hb)
  intro hu
  have heu := isUnit_of_dvd_unit he hu
  rw [Polynomial.isUnit_iff] at heu ⊢
  rcases heu with ⟨r, hur, eq_r⟩
  rw [eq_comm, expand_eq_C (zero_lt_iff.mpr hn), eq_comm] at eq_r
  exact ⟨r, hur, eq_r⟩

theorem Polynomial.flt_catalan_aux
    {p q r : ℕ} {a b c : k[X]} {u v w : k}
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q) (chr : ¬ringChar k ∣ r)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    a.natDegree = 0 := by
  cases' eq_or_ne (ringChar k) 0 with ch0 chn0
  -- characteristic zero
  · have hderiv := flt_catalan_deriv
      hp hq hr hineq chp chq chr ha hb hc hab hu hv hw heq
    rcases hderiv with ⟨da, -, -⟩
    have czk : CharZero k := by
      apply charZero_of_inj_zero
      intro n
      rw [ringChar.spec, ch0]
      exact zero_dvd_iff.mp
    rw [eq_C_of_derivative_eq_zero da]
    exact natDegree_C _
  -- characteristic p > 0
  · set d := a.natDegree with eq_d; clear_value d
    -- set up infinite descent
    -- strong induct on `d := a.natDegree`
    revert ha hb hc hab heq
    revert eq_d
    revert a b c
    induction' d using Nat.case_strong_induction_on with d ih_d
    · intros; solve_by_elim
    · intros a b c eq_d heq ha hb hc hab
      -- have derivatives of `a, b, c` zero
      have hderiv := flt_catalan_deriv
        hp hq hr hineq chp chq chr ha hb hc hab hu hv hw heq
      rcases hderiv with ⟨ad, bd, cd⟩
      -- find contracts `ca, cb, cc` so that `a(k) = ca(k^ch)`
      rcases find_contract ha ad chn0 with ⟨ca, ca_nz, eq_a, eq_deg_a⟩
      rcases find_contract hb bd chn0 with ⟨cb, cb_nz, eq_b, eq_deg_b⟩
      rcases find_contract hc cd chn0 with ⟨cc, cc_nz, eq_c, eq_deg_c⟩
      set ch := ringChar k with eq_ch
      suffices hca : ca.natDegree = 0 by
        rw [eq_d, eq_deg_a, hca, zero_mul]
      by_contra hnca; apply hnca
      apply ih_d _ _ rfl _ ca_nz cb_nz cc_nz <;> clear ih_d <;> try rfl
      · apply is_coprime_of_expand chn0
        rw [← eq_a, ← eq_b]
        exact hab
      · have _ : ch ≠ 1 := CharP.ringChar_ne_one
        have hch2 : 2 ≤ ch := by omega
        rw [← add_le_add_iff_right 1, eq_d, eq_deg_a]
        refine le_trans ?_ (Nat.mul_le_mul_left _ hch2)
        omega
      · rw [eq_a, eq_b, eq_c, ← expand_C ch u, ← expand_C ch v, ← expand_C ch w] at heq
        simp_rw [← map_pow, ← map_mul, ← map_add] at heq
        rw [Polynomial.expand_eq_zero (zero_lt_iff.mpr chn0)] at heq
        exact heq

-- Nonsolvability of Fermat-Catalan equation.
theorem Polynomial.flt_catalan
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q) (chr : ¬ringChar k ∣ r)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  -- WLOG argument: essentially three times flt_catalan_aux
  have hbc : IsCoprime b c := by
    apply rot_coprime heq hab <;> assumption
  have heq' : C v * b ^ q + C w * c ^ r + C u * a ^ p = 0 := by
    rw [add_rotate] at heq; exact heq
  have hca : IsCoprime c a := by
    apply rot_coprime heq' hbc <;> assumption
  refine ⟨?_, ?_, ?_⟩
  · apply flt_catalan_aux heq <;> assumption
  · rw [add_rotate] at heq hineq
    rw [mul_rotate] at hineq
    apply flt_catalan_aux heq <;> assumption
  · rw [← add_rotate] at heq hineq
    rw [← mul_rotate] at hineq
    apply flt_catalan_aux heq <;> assumption

/- FLT is special case of nonsolvability of Fermat-Catalan equation.
Take p = q = r = n and u = v = 1, w = -1.
-/
theorem Polynomial.flt
    {n : ℕ} (hn : 3 ≤ n) (chn : ¬ringChar k ∣ n)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have hn' : 0 < n := by linarith
  rw [← sub_eq_zero, ← one_mul (a ^ n), ← one_mul (b ^ n), ← one_mul (c ^ n), sub_eq_add_neg, ←
    neg_mul] at heq
  have hone : (1 : k[X]) = C 1 := by rfl
  have hneg_one : (-1 : k[X]) = C (-1) := by simp only [map_neg, map_one]
  simp_rw [hneg_one, hone] at heq
  apply flt_catalan hn' hn' hn' _
    chn chn chn ha hb hc hab one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq
  have eq_lhs : n * n + n * n + n * n = 3 * n * n := by ring_nf
  rw [eq_lhs]; rw [mul_assoc, mul_assoc]
  apply Nat.mul_le_mul_right (n * n); exact hn

theorem fermatLastTheoremPolynomial {n : ℕ} (hn : 3 ≤ n) (chn : ¬ringChar k ∣ n):
    FermatLastTheoremWith' k[X] n := by
  rw [FermatLastTheoremWith']
  intros a b c ha hb hc heq
  rcases gcd_dvd_left a b with ⟨a', eq_a⟩
  rcases gcd_dvd_right a b with ⟨b', eq_b⟩
  set d := gcd a b
  have hd : d ≠ 0 := gcd_ne_zero_of_left ha
  rw [eq_a, eq_b, mul_pow, mul_pow, ← mul_add] at heq
  have hdc : d ∣ c := by
    have hn : 0 < n := by omega
    have hdncn : d^n ∣ c^n := ⟨_, heq.symm⟩

    rw [dvd_iff_normalizedFactors_le_normalizedFactors hd hc]
    rw [dvd_iff_normalizedFactors_le_normalizedFactors
          (pow_ne_zero n hd) (pow_ne_zero n hc),
        normalizedFactors_pow, normalizedFactors_pow] at hdncn
    simp_rw [Multiset.le_iff_count, Multiset.count_nsmul,
      mul_le_mul_left hn] at hdncn ⊢
    exact hdncn
  rcases hdc with ⟨c', eq_c⟩
  rw [eq_a, mul_ne_zero_iff] at ha
  rw [eq_b, mul_ne_zero_iff] at hb
  rw [eq_c, mul_ne_zero_iff] at hc
  rw [mul_comm] at eq_a eq_b eq_c
  refine ⟨d, a', b', c', ⟨eq_a, eq_b, eq_c⟩, ?_⟩
  rw [eq_c, mul_pow, mul_comm, mul_left_inj' (pow_ne_zero n hd)] at heq
  suffices goal : a'.natDegree = 0 ∧ b'.natDegree = 0 ∧ c'.natDegree = 0 by
    simp [natDegree_eq_zero] at goal
    rcases goal with ⟨⟨ca', ha'⟩, ⟨cb', hb'⟩, ⟨cc', hc'⟩⟩
    rw [← ha', ← hb', ← hc']
    rw [← ha', C_ne_zero] at ha
    rw [← hb', C_ne_zero] at hb
    rw [← hc', C_ne_zero] at hc
    exact ⟨ha.right.isUnit_C, hb.right.isUnit_C, hc.right.isUnit_C⟩
  apply flt hn chn ha.right hb.right hc.right _ heq
  convert isCoprime_div_gcd_div_gcd _
  · exact EuclideanDomain.eq_div_of_mul_eq_left ha.left eq_a.symm
  · exact EuclideanDomain.eq_div_of_mul_eq_left ha.left eq_b.symm
  · rw [eq_b]
    exact mul_ne_zero hb.right hb.left

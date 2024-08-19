import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

def IntegralMatrices (m : ℤ) := { A : Matrix n n R // A.det = m }

lemma ext' (m : ℤ) {A B : IntegralMatrices n R m} (h : A.1 = B.1) : A = B := by
  cases A; cases B
  simp at *
  congr

@[ext]
lemma ext (m : ℤ) {A B : IntegralMatrices n R m} (h : ∀ i j , A.1 i j = B.1 i j) : A = B := by
  apply ext'
  ext i j
  apply h

open ModularGroup Matrix SpecialLinearGroup MatrixGroups

local notation:1024 "↑ₘ" A:1024 => ((A : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2)  ℤ)

local notation:1024 "Δ" m : 1024 => (IntegralMatrices (Fin 2) ℤ m)

lemma S_pow_two : ↑ₘ(S ^ 2) = -1 := by
  simp_rw [S, pow_two]
  simp
  exact Eq.symm (eta_fin_two (-1))

def reps (m : ℤ) : Set (Δ m) :=
  { A : Δ m | (A.1 1 0) = 0 ∧ 0 < A.1 0 0 ∧ 0 ≤ A.1 0 1 ∧  |(A.1 0 1)| < |(A.1 1 1)|}

variable (m : ℤ) (g : SpecialLinearGroup n R) (A : Δ m) (R : Type*) [CommRing R]

instance (m : outParam ℤ)  : HSMul (SpecialLinearGroup n R) (IntegralMatrices n R m)
  ((IntegralMatrices n R m)) :=
{ hSMul := fun g A => ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩}

lemma smul_def (m : ℤ) (g : SpecialLinearGroup n R) (A : (IntegralMatrices n R m)) : g • A =
  ⟨g * A.1, by simp only [det_mul, SpecialLinearGroup.det_coe, A.2, one_mul]⟩ := rfl

instance (m : ℤ) :
 MulAction (SpecialLinearGroup n R) (IntegralMatrices n R m):=
{ smul := fun g A => g • A
  one_smul := by intro b; rw [smul_def]; simp
  mul_smul := by
      intro x y b
      simp_rw [smul_def, ←mul_assoc]
      rfl
 }

lemma smul_coe (m : ℤ) (g : SpecialLinearGroup n R) (A : (IntegralMatrices n R m)) :
  (g • A).1 = g * A.1 := by
  rw [smul_def]

lemma aux1 (m : ℤ)  (A : Δ m) :
  A.1 0 0 -( A.1 1 0)*(A.1 0 0/ A.1 1 0)= A.1 0 0 % A.1 1 0:= by
  simp only [Int.cast_id, Fin.isValue]
  exact Eq.symm (Int.emod_def (A.1 0 0) (A.1 1 0))

/--Reduction step to matrices in `Mat m` which moves the matrices towars `reps`.-/
def reduce_step (A : Δ m) : Δ m :=  S • ( (T^(-((A.1 0 0)/(A.1 1 0)))) • A)

lemma reduce_aux (m : ℤ) (A : Δ m) (h : Int.natAbs (A.1 1 0) ≠ 0) :
  Int.natAbs ((reduce_step m A).1 1 0) < Int.natAbs (A.1 1 0) := by
  rw [reduce_step]
  have ha : A.1 1 0 ≠ 0 := by
    exact Int.natAbs_ne_zero.mp h
  simp only [Int.cast_id, Fin.isValue,gt_iff_lt]
  have h1 := aux1 m A
  simp_rw [smul_coe]
  rw [coe_T_zpow]
  rw [S]
  simp only [Int.reduceNeg, Fin.isValue, Int.cast_id, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    empty_mul, Equiv.symm_apply_apply, vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul,
    one_smul, empty_vecMul, add_zero, zero_add, of_apply, cons_val', Pi.neg_apply, empty_val',
    cons_val_fin_one, cons_val_one, head_fin_const, gt_iff_lt]
  rw [vecMul]
  simp [vecHead, vecTail]
  rw [mul_comm]
  rw [← @Int.sub_eq_add_neg, h1]
  have := Int.mod_lt_of_pos
  have :=  Int.emod_lt (A.1 0 0) ha
  zify
  apply le_trans _ this
  simp
  have := Int.emod_nonneg (A.1 0 0) ha
  have := abs_eq_self.mpr this
  rw [this]

@[elab_as_elim]
def reduce_rec {C : Δ m → Sort*}
(h0 : ∀ A : Δ m, Int.natAbs (A.1 1 0) = 0 → C A)
(h1 : ∀ A : Δ m, Int.natAbs ((A.1 1 0)) ≠ 0 → C (reduce_step m A) → C A): ∀ A, C A := fun A => by
    by_cases h : Int.natAbs (A.1 1 0) = 0
    · apply h0
      apply h
    · exact h1 A h (reduce_rec h0 h1 (reduce_step m A))
    termination_by A => Int.natAbs (A.1 1 0)
    decreasing_by
      simp
      apply reduce_aux m A
      simp
      rw [@Int.natAbs_eq_zero] at h
      exact h

set_option linter.unusedVariables false in
def reduce : Δ m → Δ m := fun A => by
  if h : Int.natAbs (A.1 1 0) = 0 then
    if ha : 0 < A.1 0 0 then exact (T^(-(A.1 0 1/A.1 1 1))) • A else exact
      (T^(-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A))
  else
    exact reduce (reduce_step m A)
  termination_by b => Int.natAbs (b.1 1 0)
  decreasing_by
      simp
      apply reduce_aux m
      simp
      rw [@Int.natAbs_eq_zero] at h
      exact h

lemma reduce_eqn1 (A : Δ m) (hc : Int.natAbs (A.1 1 0) = 0) (ha : 0 < A.1 0 0) :
  reduce m A = (T^(-(A.1 0 1/A.1 1 1))) • A := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc]
  rw [if_pos ha]

lemma reduce_eqn2 (A : Δ m) (hc : Int.natAbs (A.1 1 0) = 0) (ha : ¬ 0 < A.1 0 0) :
  reduce m A = (T^(-(-A.1 0 1/ -A.1 1 1))) • ( S • ( S • A)) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_pos hc]
  rw [if_neg ha]

lemma reduce_eqn3 (A : Δ m) (hc : ¬ Int.natAbs (A.1 1 0) = 0) :
  reduce m A = reduce m (reduce_step m A) := by
  rw [reduce]
  simp only [Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, zpow_neg, Int.ediv_neg, neg_neg,
    dite_eq_ite] at *
  simp_rw [if_neg hc]

example (a b : ℤ) : a < b ↔ 0 < b - a := by
  exact Iff.symm Int.sub_pos

lemma A_d_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 1 1 ≠ 0 := by
  have := A.2
  rw [@det_fin_two, ha] at this
  simp at this
  aesop

lemma A_a_ne_zero (A : Δ m) (ha : A.1 1 0 = 0) (hm : m ≠ 0) : A.1 0 0 ≠ 0 := by
  have := A.2
  rw [@det_fin_two, ha] at this
  simp at this
  aesop

lemma A_b_eq_zero (A : Δ m) (ha : A.1 1 0 = 0)  : A.1 0 0 * A.1 1 1 = m := by
  have := A.2
  rw [@det_fin_two, ha] at this
  simp at this
  aesop

lemma reduce_mem_reps (m : ℤ) (hm : m ≠ 0)  : ∀ A : Δ m, reduce m A ∈ reps m := by
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    rw [reduce_eqn1 _ _ h h1, reps]
    simp only [Int.cast_id, Fin.isValue, zpow_neg, Set.mem_setOf_eq]
    rw [smul_coe]
    simp [coe_T_zpow, vecMul, vecHead, vecTail]
    refine ⟨ Int.natAbs_eq_zero.mp h, by simp at h; rw [h]; simp [h1], by
      apply Int.ediv_mul_le ; apply A_d_ne_zero _ _ (by simpa using h) hm, by
      rw [mul_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (A.1 0 1) (A.1 1 1)).symm]
      apply le_trans _ (Int.emod_lt (A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm))
      simp
      rw [abs_eq_self.mpr ( Int.emod_nonneg (A.1 0 1) (A_d_ne_zero _ _ (by simpa using h) hm))]⟩
    rw [reduce_eqn2 _ _ h h1, reps]
    simp only [Int.cast_id, Fin.isValue, Int.ediv_neg, neg_neg, smul_def, ← mul_assoc, coe_T_zpow,
      cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, empty_mul, Equiv.symm_apply_apply,
      vecMul_vecMul, Set.mem_setOf_eq, of_apply, cons_val', vecMul, cons_dotProduct, vecHead,
      one_mul, vecTail, Function.comp_apply, Fin.succ_zero_eq_one, dotProduct_empty, add_zero,
      zero_mul, zero_add, empty_val', cons_val_fin_one, cons_val_one, cons_val_zero]
    rw [← pow_two]
    have := S_pow_two
    simp only [coe_pow] at this
    rw [this]
    simp only [Fin.isValue, neg_mul, one_mul, neg_apply, neg_eq_zero, mul_neg,
      lt_add_neg_iff_add_lt, zero_add, le_add_neg_iff_add_le, abs_neg]
    refine ⟨Int.natAbs_eq_zero.mp h,
      by
        simp only [ne_eq, Int.cast_id, Fin.isValue, Int.natAbs_eq_zero, not_lt] at *
        rw [h]
        simp only [Fin.isValue, mul_zero, Left.neg_pos_iff]
        rw [Int.lt_iff_le_and_ne]
        refine ⟨h1, by apply A_a_ne_zero _ _ (by simpa using h) hm⟩, by
        apply Int.ediv_mul_le ; apply A_d_ne_zero _ _ (by simpa using h) hm, by
        rw [mul_comm, ← @Int.sub_eq_add_neg, (Int.emod_def (-A.1 0 1) (A.1 1 1)).symm]
        have :=  Int.emod_lt (-A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm)
        apply le_trans _ (Int.emod_lt (-A.1 0 1) (by apply A_d_ne_zero _ _ (by simpa using h) hm))
        simp
        rw [abs_eq_self.mpr (Int.emod_nonneg (-A.1 0 1) (A_d_ne_zero _ _ (by simpa using h) hm))]⟩
  · intro A h1 h2
    rw [reduce_eqn3]
    exact h2
    exact h1

lemma S_smul_four (A : Δ m) : (S • ( S • (S • ( S • A)))) = A := by sorry

lemma T_S_rel (A : Δ m) : (S • S • S • T • S • T • S • A) = T⁻¹ • A := by sorry

@[elab_as_elim]
theorem induction_on {C : Δ m → Prop} (A : Δ m) (hm : m ≠ 0)
  (h0 : ∀ A : Δ m, A.1 1 0 = 0 → A.1 0 0 * A.1 1 1 = m → 0 < A.1 0 0 → 0 ≤ A.1 0 1 →
    Int.natAbs (A.1 0 1) < Int.natAbs (A.1 1 1) → C A)
  (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C ( T • B)) : C A := by
  have hS' : ∀ B, C (S • B) → C B := by
    intro B ih
    rw [← (S_smul_four m B)]
    apply hS _ (hS _ (hS _ ih))
  have hT_inv : ∀ B, C B → C (T⁻¹ • B) := by
    intro B ih
    have h := (hS _ $ hS _ $ hS _ $ hT _ $ hS _ $ hT _ $ hS _ ih)
    rw [T_S_rel m B] at h
    exact h
  have hT' : ∀ B, C (T • B) → C B := by
    intro B ih
    have h := hT_inv (T • B) ih
    simpa using h
  have hT_pow' : ∀ B (n : ℤ), C ((T^n) • B) → C B := by
    intro B n
    induction' n using Int.induction_on with n hn m hm
    · simp only [ne_eq, Int.cast_id, Fin.isValue, zpow_zero, one_smul, imp_self] at *
    ·   intro h
        rw [add_comm, zpow_add, ← smul_eq_mul] at h
        simp only [zpow_one] at h
        rw [smul_assoc] at h
        exact hn $ hT' _ h
    · rw [sub_eq_neg_add, zpow_add, zpow_neg_one]
      intro h
      apply hm
      have := hT _ h
      rw [smul_def] at this
      convert this
      simp only [zpow_neg, zpow_natCast, smul_def, Int.cast_id, coe_inv, coe_pow, adjugate_pow, ←
        mul_assoc, ← coe_mul, mul_inv_cancel T, one_mul]
  have h_reduce : C (reduce m A) := by
    rcases reduce_mem_reps m hm A with ⟨H1, H2, H3, H4⟩
    apply h0 _ H1 ?_ H2 H3
    · zify
      apply H4
    · apply A_b_eq_zero _ _ H1
  suffices  ∀ A : Δ m, C (reduce m A) → C A from this _ h_reduce
  apply reduce_rec
  · intro A h
    by_cases h1 : 0 < A.1 0 0
    · rw [reduce_eqn1 _ _ h h1]
      intro h
      apply hT_pow' A (-(A.1 0 1 / A.1 1 1)) h
    · rw [reduce_eqn2 _ _ h h1]
      intro h
      exact hS' _ $ hS' _ (hT_pow' _ _ h)
  intro A hc ih hA
  rw [reduce_eqn3 _ _ hc] at hA
  exact hT_pow' _ _ $ hS' _ (ih hA)


def G := Subgroup.closure {S, T}

lemma S_mem_G : S ∈ G := by
  apply Subgroup.subset_closure
  simp

lemma T_mem_G : T ∈ G := by
  apply Subgroup.subset_closure
  simp

def orbit_rel (m : ℤ) : Setoid (Δ m) where
  r := fun x y => x ∈ MulAction.orbit G y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      apply MulAction.mem_orbit_self
    · intro x y
      exact fun a ↦ (MulAction.mem_orbit_symm.mp) a
    · intro x y z hxy hyz
      rw [@MulAction.mem_orbit_iff] at *
      obtain ⟨g, hg⟩ := hxy
      obtain ⟨h, hh⟩ := hyz
      refine ⟨g • h, ?_⟩
      rw [smul_assoc, hh, hg]

theorem reduce_spec (m : ℤ) : ∀A : Δ m, ∃ (R: G), R • A = reduce m A := by
    apply reduce_rec
    intro A hc
    by_cases h : 0 < (A.1 0 0)
    rw [reduce_eqn1 _ _ hc h]
    refine ⟨⟨T ^ (-(A.1 0 1 / A.1 1 1)), ?_⟩, ?_⟩
    refine Subgroup.zpow_mem G ?_ (-(A.1 0 1 / A.1 1 1))
    rw [G]
    apply Subgroup.subset_closure
    simp
    rfl
    simp
    rw [reduce_eqn2 _ _ hc h]
    refine ⟨T ^ (-(-A.1 0 1 / -A.1 1 1)) • S • S, ?_, ?_⟩
    simp
    apply Subgroup.mul_mem
    refine Subgroup.zpow_mem G ?_ _
    apply Subgroup.subset_closure
    simp
    apply Subgroup.mul_mem
    apply Subgroup.subset_closure
    simp
    apply Subgroup.subset_closure
    simp
    simp_rw [smul_assoc]
    intro A ha
    rw [reduce_eqn3 _ _ ha]
    intro ht
    obtain ⟨R, hR⟩ := ht
    rw [reduce_step] at *
    refine ⟨⟨R • S • T ^ (-((A.1 0 0) / (A.1 1 0))), ?_⟩, ?_⟩
    simp
    apply Subgroup.mul_mem
    simp
    apply Subgroup.mul_mem
    apply S_mem_G
    simp
    apply Subgroup.zpow_mem G T_mem_G
    rw [← hR]
    simp
    simp_rw [smul_def]
    simp_rw [← mul_assoc]
    simp

lemma c2 (B : Δ 1) (hB : B ∈  G) : (S • B) ∈ G := by sorry

lemma test : ∀ A : Δ 1, A ∈ G := by
  intro A
  induction A using (induction_on 1 )
  exact Int.one_ne_zero
  next A a1 a2 a4 a5 a6 =>
    have : A = (1 : SL(2,ℤ)) := by
      ext i j
      fin_cases i; fin_cases j
      simp

      sorry
      simp

      sorry
      fin_cases j
      simp [a1]
      simp


    rw [this]
    exact Subgroup.one_mem G

  next B hb => apply (c2 B) hb
  next B hb => sorry



theorem reps_unique' (m : ℤ) (hm : m ≠ 0) :
  ∀(M : G) (A B : Δ m), A ∈ reps m → B ∈ reps m →  M • A = B → A = B := by
  intro M A B hA hB h
  rw [← h]
  simp [reps] at *

  sorry


/-
begin
  rintros  M A B
    ⟨g_eq, e_pos, f_nonneg, f_bound⟩ ⟨k_eq, H6, f'_nonneg, f'_bound⟩ B_eq, rw ← B_eq,
    rw m_a_b' at B_eq,
  have ht: M 1 0 = 0,
    {rw [k_eq, g_eq] at B_eq,
    simp only [add_zero, zero_eq_mul, mul_zero] at B_eq,
    cases B_eq.2.2.1,
    exact h,
    rw h at e_pos,
    exact (irrefl _ e_pos).elim, },
  have d1: (M 0 0)*(M 1 1)=1,
    by {have:= matrix.det_fin_two M, simp at *, rw ht at this, simp at this,
      have hm:= gengroup_det M, rw hm at this, apply this.symm, },
  have mg0: (M  0 0) > 0, by
    {rw g_eq at B_eq, simp only [add_zero, mul_zero] at B_eq,
    exact one_time (B 0 0) (M 0 0) (A 0 0) H6 e_pos B_eq.1, },
  have htt: M 0 0 =1 ∧ M 1 1 =1, by
    { rw int.mul_eq_one at d1, apply one_time' (M 0 0) (M 1 1) mg0 d1,},
  have httv: M 1 1 =1, { simp only [htt], },
  have htv: ((A 0 1)+ (M 0 1)*(A 1 1)) ≥ 0, by
    {rw B_eq.2.1 at f'_nonneg,
    rw htt.1 at f'_nonneg,
    simp only [one_mul] at f'_nonneg,
    exact f'_nonneg},
  have httt: M 0 1 =0, by
    {rw B_eq.2.2.2 at f'_bound,
    rw B_eq.2.1 at f'_bound,
    rw ht at f'_bound,
    rw htt.1 at f'_bound,
    rw httv at f'_bound,
    simp only [one_mul, zero_mul,
    zero_add] at f'_bound,
    apply num_gt_sum (A 1 1) (A 0 1) (M 0 1)  f_nonneg  f_bound htv,
    exact f'_bound, },
  have M1: ↑M = (1: SL2Z), by
      {ext i j,
      fin_cases i;
      fin_cases j,
      exact htt.1,
      exact  httt,
      exact ht,
      exact httv},
    norm_cast at M1,
    rw M1,
    simp only [one_smul],
    exact hm,
end -/



def reps_equiv' (hm : m ≠ 0) : Quotient (orbit_rel m ) ≃ reps m where
  toFun := fun A => Quotient.liftOn A (fun A => ⟨reduce m A, reduce_mem_reps m hm A⟩)
    (by
      intro A B ⟨h, a⟩
      simp
      obtain ⟨R, hR⟩ := reduce_spec m A
      obtain ⟨S, hS⟩ := reduce_spec m B
      simp at a
      apply reps_unique' m hm ( S • h⁻¹ • R⁻¹) _ _ (reduce_mem_reps m hm A) (reduce_mem_reps m hm B)
      rw [← hR, ← hS, ← a]
      simp_rw [smul_assoc]
      simp)
  invFun := fun A => ⟦A⟧
  left_inv := by
    intro a
    letI := orbit_rel m
    simp
    rw [Quotient.mk_eq_iff_out]
    rcases a with ⟨A, hA⟩
    simp
    have : (Quotient.out (s:= orbit_rel m) (Quot.mk _ ⟨A, hA⟩)) ≈ ⟨A, hA⟩ := by
      exact Quotient.eq_mk_iff_out.mp rfl
    apply Setoid.trans (b := ⟨A, hA⟩)
    have := reduce_spec m ⟨A, hA⟩
    obtain ⟨R, hR⟩ := this
    use R
    exact id (Setoid.symm this)
  right_inv := by
    intro a
    apply Subtype.eq
    simp only [Quotient.lift_mk]
    have := reduce_spec m a
    obtain ⟨R, hR⟩ := this
    apply reps_unique' m hm R⁻¹
    exact reduce_mem_reps m hm a
    exact a.2
    rw [← hR]
    simp

lemma sl2_eq_mat_1 : SL(2,ℤ) = Δ 1 := by
  rw [IntegralMatrices]
  rfl

def reps_equiv_group_quot : Quotient (orbit_rel 1) ≃ SL(2,ℤ) ⧸ G := by
  have : (SL(2,ℤ) ⧸ G) = ((Δ 1) ⧸ G) := by
    congr
  have := QuotientGroup.quotientRightRelEquivQuotientLeftRel G
  exact this

lemma reps_sl : reps 1 = {(1 : SL(2,ℤ))} := by
  rw [reps]
  ext A
  constructor
  intro h
  simp at *
  /- ext i j
  fin_cases i; fin_cases j;
  simp
   -/

  sorry
  sorry



lemma SL2Z_generators : G = (⊤ : Subgroup (SL(2,ℤ)))  := by
  apply QuotientGroup.subgroup_eq_top_of_subsingleton
  have : (SL(2,ℤ) ⧸ G) =
    Quotient (QuotientGroup.leftRel (Subgroup.closure {S, T})) := by rfl
  let t := reps_equiv_group_quot
  rw [← (Equiv.subsingleton_congr t)]
  let t2 := (reps_equiv' 1 (Int.one_ne_zero))
  rw [(Equiv.subsingleton_congr t2)]
  rw [reps_sl]
  simp

/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.DirectSum.Basic

/-!
# Functoriality of adic completions

In this file we establish functorial properties of the adic completion.

## Main definitions

- `LinearMap.adicCauchy I f`: the by `f` induced linear map on `I`-adic cauchy sequences
- `LinearMap.adicCompletion I f`: the by `f` induced linear map on `I`-adic completions

## Main results

-/

variable {R : Type*} [CommRing R] (I : Ideal R)

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

attribute [-simp] smul_eq_mul Algebra.id.smul_eq_mul

/-- `R`-linear version of `reduceModIdeal`. -/
private def reduceModIdealAux (f : M →ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) →ₗ[R] N ⧸ (I • ⊤ : Submodule R N) :=
  Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
    (fun x hx ↦ by
      refine Submodule.smul_induction_on hx (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
      · simp [Submodule.smul_mem_smul hr Submodule.mem_top]
      · simp [Submodule.add_mem _ hx hy])

@[simp]
private theorem reduceModIdealAux_apply (f : M →ₗ[R] N) (x : M) :
    (f.reduceModIdealAux I) (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R N)) (f x) :=
  rfl

/-- The induced linear map on the quotients mod `I • ⊤`. -/
def reduceModIdeal (f : M →ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) →ₗ[R ⧸ (I • ⊤ : Ideal R)] N ⧸ (I • ⊤ : Submodule R N) where
  toFun := f.reduceModIdealAux I
  map_add' := by simp
  map_smul' r x := by
    refine Quotient.inductionOn' r (fun r ↦ ?_)
    refine Quotient.inductionOn' x (fun x ↦ ?_)
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk,
      RingHomCompTriple.comp_apply, reduceModIdealAux_apply]
    rw [AdicCompletion.mk_smul_mk, AdicCompletion.mk_smul_mk]
    simp only [LinearMapClass.map_smul, reduceModIdealAux_apply]

@[simp]
theorem reduceModIdeal_apply (f : M →ₗ[R] N) (x : M) :
    (f.reduceModIdeal I) (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R N)) (f x) :=
  rfl

open AdicCompletion

/-- A linear map induces a linear map on adic cauchy sequences. -/
@[simps]
def adicCauchy (f : M →ₗ[R] N) : AdicCauchySequence I M →ₗ[R] AdicCauchySequence I N where
  toFun a := ⟨fun n ↦ f (a n), fun {m n} hmn ↦ by
    have hm : Submodule.map f (I ^ m • ⊤ : Submodule R M) ≤ (I ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    apply SModEq.mono hm
    apply SModEq.map (a.property hmn) f⟩
  map_add' a b := by ext n; simp
  map_smul' r a := by ext n; simp

variable (M) in
theorem adicCauchy_id : adicCauchy I (LinearMap.id (M := M)) = LinearMap.id :=
  rfl

variable (M N) in
theorem adicCauchy_zero : adicCauchy I (0 : M →ₗ[R] N) =
    (0 : AdicCauchySequence I M →ₗ[R] AdicCauchySequence I N) :=
  rfl

@[simp]
theorem adicCauchy_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    g.adicCauchy I ∘ₗ f.adicCauchy I = (g ∘ₗ f).adicCauchy I :=
  rfl

theorem adicCauchy_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (a : AdicCauchySequence I M) :
    g.adicCauchy I (f.adicCauchy I a) = (g ∘ₗ f).adicCauchy I a :=
  rfl

theorem AdicCompletion.transitionMap_comp_reduceModIdeal (f : M →ₗ[R] N) {m n : ℕ}
    (hmn : m ≤ n) : transitionMap I N hmn ∘ₗ reduceModIdeal (I ^ n) f =
      (f.reduceModIdeal (I ^ m) : _ →ₗ[R] _) ∘ₗ transitionMap I M hmn := by
  ext x
  simp

/-- `R`-linear version of `adicCompletion`. -/
private def adicCompletionAux (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[R] AdicCompletion I N :=
  AdicCompletion.lift I (fun n ↦ reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn ↦ by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, transitionMap_comp_eval])

@[simp]
theorem adicCompletionAux_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (f.adicCompletionAux I x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

/-- A linear map induces a map on adic completions. -/
def adicCompletion (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  toFun := f.adicCompletionAux I
  map_add' := by aesop
  map_smul' r x := by
    ext n
    simp only [adicCompletionAux_val_apply, smul_eval, LinearMapClass.map_smul, RingHom.id_apply]

@[simp]
theorem adicCompletion_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (f.adicCompletion I x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
theorem AdicCompletion.ext {f g : AdicCompletion I M → N}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x (fun a ↦ h a)

theorem AdicCompletion.ext' {f g : AdicCompletion I M →ₗ[R] N}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x (fun a ↦ h a)

@[ext]
theorem AdicCompletion.ext'' {f g : AdicCompletion I M →ₗ[AdicCompletion I R] T}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x (fun a ↦ h a)

variable (M) in
@[simp]
theorem adicCompletion_id :
    adicCompletion I (LinearMap.id (M := M)) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I M) := by
  ext
  simp

variable (M N) in
@[simp]
theorem adicCompletion_zero : adicCompletion I (0 : M →ₗ[R] N) =
    (0 : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) := by
  ext
  simp

@[simp]
theorem adicCompletion_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    g.adicCompletion I ∘ₗ f.adicCompletion I = (g ∘ₗ f).adicCompletion I := by
  ext
  simp

@[simp]
theorem adicCompletion_mk (f : M →ₗ[R] N) (a : AdicCauchySequence I M) :
    f.adicCompletion I (AdicCompletion.mk I M a) =
      AdicCompletion.mk I N (f.adicCauchy I a) :=
  rfl

@[simp]
theorem val_sum {α : Type*} (s : Finset α) (f : α → AdicCompletion I M) (n : ℕ) :
    (Finset.sum s f).val n = Finset.sum s (fun a ↦ (f a).val n) := by
  change (Submodule.subtype (AdicCompletion.submodule I M) _) n = _
  rw [map_sum, Finset.sum_apply, Submodule.coeSubtype]

end LinearMap

namespace LinearEquiv

variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]

/-- A linear equiv induces a linear equiv on adic completions. -/
def adicCompletion (f : M ≃ₗ[R] N) :
    AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N :=
  LinearEquiv.ofLinear (f.toLinearMap.adicCompletion I)
    (f.symm.toLinearMap.adicCompletion I) (by simp) (by simp)

theorem adicCompletion_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I M) :
    f.adicCompletion I x = f.toLinearMap.adicCompletion I x :=
  rfl

theorem adicCompletion_symm_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I N) :
    (f.adicCompletion I).symm x = f.symm.toLinearMap.adicCompletion I x :=
  rfl

@[simp]
theorem adicCompletion_val_apply (f : M ≃ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (f.adicCompletion I x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

end LinearEquiv

namespace AdicCompletion

section Families

/-! ### Adic completion in families

In this section we consider a family `M : ι → Type*` of `R`-modules. Purely from
the formal properties of adic completions we obtain two canonical maps

- `AdicCompleiton I (∀ j, M j) →ₗ[R] ∀ j, AdicCompletion I (M j)`
- `(⨁ j, (AdicCompletion I (M j))) →ₗ[R] AdicCompletion I (⨁ j, M j)`

If `ι` is finite, both are isomorphisms and, modulo
the equivalence `⨁ j, (AdicCompletion I (M j)` and `∀ j, AdicCompletion I (M j)`,
inverse to each other.

-/

variable {ι : Type*} [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)]

section Pi

/-- The canonical map from the adic completion of the product to the product of the
adic completions. -/
@[simps!]
def pi : AdicCompletion I (∀ j, M j) →ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  LinearMap.pi (fun j ↦ (LinearMap.proj j).adicCompletion I)

end Pi

section Sum

open DirectSum

/-- The canonical map from the sum of the adic completions to the adic completion
of the sum. -/
def sum :
    (⨁ j, (AdicCompletion I (M j))) →ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  toModule (AdicCompletion I R) ι (AdicCompletion I (⨁ j, M j))
    (fun j ↦ (lof R ι M j).adicCompletion I)

@[simp]
theorem sum_lof (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.lof (AdicCompletion I R) ι (fun i ↦ AdicCompletion I (M i)) j) x) =
      (lof R ι M j).adicCompletion I x := by
  simp [sum]

@[simp]
theorem sum_of (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.of (fun i ↦ AdicCompletion I (M i)) j) x) =
      (lof R ι M j).adicCompletion I x := by
  rw [← lof_eq_of R]
  apply sum_lof

variable [Fintype ι]

/-- If `ι` is finite, we use the equivalence of sum and product to obtain an inverse for
`AdicCompletion.sum` from `AdicCompletion.pi`. -/
def sumInv : AdicCompletion I (⨁ j, M j) →ₗ[AdicCompletion I R] (⨁ j, (AdicCompletion I (M j))) :=
  let f := (linearEquivFunOnFintype R ι M).adicCompletion I
  let g := linearEquivFunOnFintype (AdicCompletion I R) ι (fun j ↦ AdicCompletion I (M j))
  g.symm.toLinearMap ∘ₗ pi I M ∘ₗ f

@[simp]
theorem component_sumInv (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    component (AdicCompletion I R) ι _ j (sumInv I M x) =
      (component R ι _ j).adicCompletion I x := by
  apply induction_on I _ x (fun x ↦ ?_)
  rfl

@[simp]
theorem sumInv_apply (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    (sumInv I M x) j = (component R ι _ j).adicCompletion I x := by
  apply induction_on I _ x (fun x ↦ ?_)
  rfl

theorem sumInv_comp_sum : sumInv I M ∘ₗ sum I M = LinearMap.id := by
  ext j x
  apply DirectSum.ext (AdicCompletion I R) (fun i ↦ ?_)
  ext n
  simp only [LinearMap.coe_comp, Function.comp_apply, sum_lof, LinearMap.adicCompletion_mk,
    component_sumInv, mk_apply_coe, LinearMap.adicCauchy_apply_coe, Submodule.mkQ_apply,
    LinearMap.id_comp]
  rw [DirectSum.component.of, DirectSum.component.of]
  split
  · next h => subst h; simp
  · simp

theorem sum_comp_sumInv : sum I M ∘ₗ sumInv I M = LinearMap.id := by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of _ (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι), M j)) f)))]
  simp only [sumInv_apply, LinearMap.adicCompletion_mk, map_sum, sum_of, LinearMap.val_sum,
    mk_apply_coe, LinearMap.adicCauchy_apply_coe, Submodule.mkQ_apply]
  simp only [← Submodule.mkQ_apply, ← map_sum]
  erw [DirectSum.sum_univ_of]

/-- If `ι` is finite, `sum` has `sumInv` as inverse. -/
def sumEquivOfFintype :
    (⨁ j, (AdicCompletion I (M j))) ≃ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  LinearEquiv.ofLinear (sum I M) (sumInv I M) (sum_comp_sumInv I M) (sumInv_comp_sum I M)

@[simp]
theorem sumEquivOfFintype_apply (x : ⨁ j, (AdicCompletion I (M j))) :
    sumEquivOfFintype I M x = sum I M x :=
  rfl

@[simp]
theorem sumEquivOfFintype_symm_apply (x : AdicCompletion I (⨁ j, M j)) :
    (sumEquivOfFintype I M).symm x = sumInv I M x :=
  rfl

end Sum

section Pi

open DirectSum

variable [Fintype ι]

/-- If `ι` is finite, `pi` is a linear equiv. -/
def piEquivOfFintype :
    AdicCompletion I (∀ j, M j) ≃ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  let f := ((linearEquivFunOnFintype R ι M).adicCompletion I).symm
  let g := (linearEquivFunOnFintype (AdicCompletion I R) ι (fun j ↦ AdicCompletion I (M j)))
  f.trans ((sumEquivOfFintype I M).symm.trans g)

@[simp]
theorem piEquivOfFintype_apply (x : AdicCompletion I (∀ j, M j)) :
    piEquivOfFintype I M x = pi I M x := by
  simp [piEquivOfFintype, sumInv]

/-- Adic completion of `R^n` is `(AdicCompletion I R)^n`. -/
def piEquivFin (n : ℕ) :
    AdicCompletion I (Fin n → R) ≃ₗ[AdicCompletion I R] Fin n → AdicCompletion I R :=
  piEquivOfFintype I (ι := Fin n) (fun _ : Fin n ↦ R)

@[simp]
theorem piEquivFin_apply (n : ℕ) (x : AdicCompletion I (Fin n → R)) :
    piEquivFin I n x = pi I (fun _ : Fin n ↦ R) x := by
  simp only [piEquivFin, piEquivOfFintype_apply]

end Pi

end Families

end AdicCompletion

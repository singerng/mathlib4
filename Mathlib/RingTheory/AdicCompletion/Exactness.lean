/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Filtration

/-!
# Exactness of adic completion

In this file we establish exactness properties of adic completions. In particular we show:

## Main results

- `LinearMap.adicCompletion_surjective`: Adic completion preserves surjectivity.
- `LinearMap.adicCompletion_injective`: Adic completion preserves injectivity
  of maps between finite modules over a Noetherian ring.
- `LinearMap.adicCompletion_exact`: Over a noetherian ring adic completion is exact on finite
  modules.

## Implementation details

All results are proven directly without using Mittag-Leffler systems.

-/

universe u v w t

open AdicCompletion

section Surjectivity

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

variable {f : M →ₗ[R] N} (hf : Function.Surjective f)

/- In each step, a preimage is constructed from the preimage of the previous step by
subtracting this delta. -/
private noncomputable def LinearMap.adicCompletionPreimageDelta (x : AdicCauchySequence I N)
    {n : ℕ} {y yₙ : M} (hy : f y = x (n + 1)) (hyₙ : f yₙ = x n) :
    { d : (I ^ n • ⊤ : Submodule R M) | f d = f (yₙ - y) } := by
  suffices h : f (yₙ - y) ∈ Submodule.map f (I ^ n • ⊤ : Submodule R M) by
    choose d dmem hd using h
    exact ⟨⟨d, dmem⟩, hd⟩
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf, map_sub,
    hyₙ, hy, ← Submodule.neg_mem_iff, neg_sub, ← SModEq.sub_mem]
  exact AdicCauchySequence.mk_eq_mk (Nat.le_succ n) x

/- Inductively construct preimage of cauchy sequence. -/
private noncomputable def LinearMap.adicCompletionPreimage (x : AdicCauchySequence I N) :
    (n : ℕ) → f ⁻¹' {x n}
  | .zero => ⟨(hf (x 0)).choose, (hf (x 0)).choose_spec⟩
  | .succ n => by
      choose y hy using hf (x (n + 1))
      let ⟨yₙ, (hyₙ : f yₙ = x n)⟩ := adicCompletionPreimage x n
      let ⟨⟨d, _⟩, (p : f d = f (yₙ - y))⟩ := adicCompletionPreimageDelta hf x hy hyₙ
      exact ⟨yₙ - d, by simpa [p]⟩

variable (I)

/-- Adic completion preserves surjectivity -/
theorem LinearMap.adicCompletion_surjective :
    Function.Surjective (f.adicCompletion I) := fun y ↦ by
  apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
  let a := LinearMap.adicCompletionPreimage hf b
  refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n ↦ (a n : M)) ?_), ?_⟩
  · refine fun n ↦ SModEq.symm ?_
    simp only [SModEq.symm, SModEq, adicCompletionPreimage, Submodule.Quotient.mk_sub,
      sub_eq_self, Submodule.Quotient.mk_eq_zero, SetLike.coe_mem, a]
  · exact _root_.AdicCompletion.ext fun n ↦ congrArg _ ((a n).property)

end Surjectivity

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N]
variable {P : Type u} [AddCommGroup P] [Module R P]

section Injectivity

variable [IsNoetherianRing R] [Module.Finite R N]

/-- Adic completion preserves injectivity of finite modules over a Noetherian ring. -/
theorem LinearMap.adicCompletion_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.adicCompletion I) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨42, fun n _ ↦ ⟨n + k, by omega, n, by omega, ?_⟩⟩
  rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M),
    Submodule.map_smul'', Submodule.map_top]
  apply (smul_mono_right _ inf_le_right : I ^ n • (I ^ k • ⊤ ⊓ (range f)) ≤ _)
  nth_rw 2 [show n = n + k - k by omega]
  rw [← hk (n + k) (show n + k ≥ k by omega)]
  refine ⟨?_, ⟨a (n + k), rfl⟩⟩
  simpa using congrArg (fun x ↦ x.val (n + k)) hx

end Injectivity

section

variable [IsNoetherianRing R] [Module.Finite R N]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

section

variable {I} {k : ℕ}
  (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
  (x : AdicCauchySequence I N)
  (hker : ∀ (n : ℕ), g (x n) ∈ (I ^ n • ⊤ : Submodule R P))

/- In each step, a preimage is constructed from the preimage of the previous step by
adding this delta. -/
private noncomputable def LinearMap.adicCompletionExactAuxDelta {n : ℕ} {d : N}
    (hdmem : d ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N)) {y yₙ : M}
    (hd : f y = x (k + n + 1) - d) (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N)) :
    { d : (I ^ n • ⊤ : Submodule R M)
      | f (yₙ + d) - x (k + n + 1) ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N) } := by
  have h : f (y - yₙ) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp only [map_sub, hd]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) ∈ I ^ (k + n) • ⊤
    · abel
    · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
      · rw [← Submodule.Quotient.eq]
        exact AdicCauchySequence.mk_eq_mk (by omega) _
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) hdmem
  have hincl : I ^ (k + n - k) • (I ^ k • ⊤ ⊓ range f) ≤ I ^ (k + n - k) • (range f) :=
    smul_mono_right _ inf_le_right
  refine ⟨⟨y - yₙ, ?_⟩, ?_⟩
  · convert_to y - yₙ ∈ (I ^ (k + n - k) • ⊤ : Submodule R M)
    · simp
    · rw [← Submodule.comap_map_eq_of_injective hf (I ^ (k + n - k) • ⊤ : Submodule R M),
        Submodule.map_smul'', Submodule.map_top]
      apply hincl
      rw [← hkn (k + n) (by omega)]
      exact ⟨h, ⟨y - yₙ, rfl⟩⟩
  · simpa [hd, Nat.succ_eq_add_one, Nat.add_assoc]

open Submodule

/- Inductively construct preimage of cauchy sequence in kernel of `g.adicCompletion I`. -/
private noncomputable def LinearMap.adicCompletionExactAux :
    (n : ℕ) → { a : M | f a - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) }
  | .zero => by
      choose d y hdmem hdy using h2 0
      exact ⟨y, by simpa [hdy]⟩
  | .succ n => by
      choose d y hdmem hdy using h2 (n + 1)
      let ⟨yₙ, (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N))⟩ :=
        adicCompletionExactAux n
      let ⟨d, hd⟩ := adicCompletionExactAuxDelta hf hkn x hdmem hdy hyₙ
      exact ⟨yₙ + d, hd⟩
 where
  h1 (n : ℕ) : g (x (k + n)) ∈ Submodule.map g (I ^ (k + n) • ⊤ : Submodule R N) := by
    rw [map_smul'', Submodule.map_top, range_eq_top.mpr hg]
    exact hker (k + n)
  h2 (n : ℕ) : ∃ (d : N) (y : M),
      d ∈ (I ^ (k + n) • ⊤ : Submodule R N) ∧ f y = x (k + n) - d := by
    obtain ⟨d, hdmem, hd⟩ := h1 n
    obtain ⟨y, hdy⟩ := (hfg (x (k + n) - d)).mp (by simp [hd])
    refine ⟨d, y, hdmem, hdy⟩

end

/-- adicCompletion over a Noetherian ring is exact on finitely generated modules. -/
theorem LinearMap.adicCompletion_exact :
    Function.Exact (LinearMap.adicCompletion I f) (LinearMap.adicCompletion I g) := by
  refine Function.Exact.of_linearMap_comp_eq_zero_of_ker_in_range ?_ (fun y ↦ ?_)
  · rw [adicCompletion_comp, hfg.linearMap_comp_eq_zero, adicCompletion_zero]
  · apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
    intro hz
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    have hb (n : ℕ) : g (b n) ∈ I ^ n • ⊤ := by simpa using congrArg (fun x ↦ x.val n) hz
    let a := adicCompletionExactAux hf hfg hg hk b hb
    refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n ↦ (a n : M)) ?_), ?_⟩
    · refine fun n ↦ SModEq.symm ?_
      simp [a, adicCompletionExactAux, SModEq]
    · ext n
      suffices h : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
            Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (k + n)) by
        simp [h, AdicCauchySequence.mk_eq_mk (show n ≤ k + n by omega)]
      rw [Submodule.Quotient.eq]
      have hle : (I ^ (k + n) • ⊤ : Submodule R N) ≤ (I ^ n • ⊤ : Submodule R N) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
      exact hle (a n).property

end

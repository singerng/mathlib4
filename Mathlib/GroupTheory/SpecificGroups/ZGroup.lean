/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Transfer

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: A predicate stating that all Sylow subgroups of `G` are cyclic.

TODO: Show that if `G` is a Z-group with commutator subgroup `G'`, then `G = G' ⋊ G/G'` where `G'`
and `G/G'` are cyclic of coprime orders.

-/

variable (G G' : Type*) [Group G] [Group G'] (f : G →* G')

/-- A Z-group is a group whose Sylow subgroups are all cyclic. -/
@[mk_iff] class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' f}

namespace IsZGroup

instance [IsZGroup G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsCyclic P :=
  isZGroup p Fact.out P

theorem of_squarefree (hG : Squarefree (Nat.card G)) : IsZGroup G := by
  have : Finite G := Nat.finite_of_card_ne_zero hG.ne_zero
  refine ⟨fun p hp P ↦ ?_⟩
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  exact isCyclic_of_card_dvd_prime ((hk ▸ hG.pow_dvd_of_pow_dvd) P.card_subgroup_dvd_card)

theorem of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G := by
  rw [isZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P ≤ Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective

instance [IsZGroup G] (H : Subgroup G) : IsZGroup H := of_injective H.subtype_injective

theorem of_surjective [Finite G] [hG : IsZGroup G] (hf : Function.Surjective f) : IsZGroup G' := by
  rw [isZGroup_iff] at hG ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

instance [Finite G] [IsZGroup G] (H : Subgroup G) [H.Normal] : IsZGroup (G ⧸ H) :=
  of_surjective (QuotientGroup.mk'_surjective H)

instance [Finite G] [IsZGroup G] : IsZGroup (Abelianization G) :=
  of_surjective (QuotientGroup.mk'_surjective (commutator G))

end IsZGroup

section Burnside

/-- The homomorphism `Normalizer(H) → Aut(H)` with kernel `Centralizer(H)`. -/
@[simps]
def Subgroup.autmap {G : Type*} [Group G] (H : Subgroup G) : H.normalizer →* MulAut H where
  toFun := fun g ↦
    { toFun := fun h ↦ ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
      invFun := fun h ↦ ⟨g⁻¹ * h * g, (mem_normalizer_iff''.mp g.2 h).mp h.2⟩
      left_inv := fun _ ↦ by simp [mul_assoc]
      right_inv := fun _ ↦ by simp [mul_assoc]
      map_mul' := by simp [mul_assoc] }
  map_one' := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff, mul_assoc]

theorem Subgroup.autmap_ker {G : Type*} [Group G] (H : Subgroup G) :
    H.autmap.ker = (Subgroup.centralizer H).subgroupOf H.normalizer := by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, mem_subgroupOf, autmap, mem_centralizer_iff,
    eq_comm, eq_mul_inv_iff_mul_eq]

def MulAut.congr {G H : Type*} [Group G] [Group H] (ϕ : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun := fun f ↦ ϕ.symm.trans (f.trans ϕ)
  invFun := fun f ↦ ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

def ringequiv (n : ℕ) : AddAut (ZMod n) ≃* (ZMod n)ˣ :=
  have key : ∀ (f : AddAut (ZMod n)) (x : ZMod n), f 1 * x = f x := by
    intro f x
    rw [mul_comm]
    have h2 := (zsmul_eq_mul (f 1) x.cast).symm
    rwa [← map_zsmul, zsmul_one, ZMod.intCast_zmod_cast] at h2
  { toFun := fun f ↦ Units.mkOfMulEqOne (f 1) (f⁻¹ 1) (by
      rw [key, f.inv_apply_self])
    invFun := AddAut.mulLeft
    left_inv := by
      intro f
      ext x
      simp [Units.smul_def, key]
    right_inv := by
      intro x
      ext
      simp [Units.smul_def]
    map_mul' := by
      intro f g
      ext
      simp [key] }

theorem IsCyclic.card_mulAut {G : Type*} [Group G] [Finite G] [h : IsCyclic G] :
    Nat.card (MulAut G) = Nat.totient (Nat.card G) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  have key := MulAut.congr (zmodCyclicMulEquiv h)
  have key3 := key.toEquiv.symm.trans (MulEquiv.toAdditive.trans (ringequiv (Nat.card G)).toEquiv)
  exact Nat.card_congr key3

theorem thm1 {G : Type*} [Group G] [Finite G] {P : Sylow (Nat.card G).minFac G} (hP : IsCyclic P) :
    P.normalizer ≤ Subgroup.centralizer (P : Set G) := by
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim P.normalizer ⊥]
    exact bot_le
  have key := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.autmap)
  rw [Subgroup.autmap_ker, ← Subgroup.index, ← Subgroup.relindex] at key
  refine Subgroup.relindex_eq_one.mp (Nat.eq_one_of_dvd_coprimes ?_ dvd_rfl key)
  have := Fact.mk (Nat.minFac_prime hn)
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  rcases eq_zero_or_pos k with h0 | h0
  · rw [hP.card_mulAut, hk, h0, pow_zero, Nat.totient_one]
    apply Nat.coprime_one_right
  rw [hP.card_mulAut, hk, Nat.totient_prime_pow (Nat.minFac_prime hn) h0,
    Nat.coprime_mul_iff_right]
  refine ⟨Nat.Coprime.pow_right _ ?_, ?_⟩
  · have key' : P.IsCommutative := by
      let h := hP.commGroup
      exact ⟨⟨CommGroup.mul_comm⟩⟩
    have key := P.le_centralizer
    replace key := Subgroup.relindex_dvd_of_le_left P.normalizer key
    apply Nat.Coprime.coprime_dvd_left key
    replace key := Subgroup.relindex_dvd_index_of_le P.le_normalizer
    apply Nat.Coprime.coprime_dvd_left key
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Nat.minFac_prime hn)]
    exact P.not_dvd_index
  · rw [Nat.Coprime]
    have h1 :=
      Nat.gcd_dvd_left ((Subgroup.centralizer P).relindex P.normalizer) ((Nat.card G).minFac - 1)
    replace h1 : ((Subgroup.centralizer P).relindex P.normalizer).gcd ((Nat.card G).minFac - 1)
      ∣ Nat.card G := by
      refine h1.trans ?_
      rw [← Subgroup.inf_relindex_left]
      exact (Subgroup.relindex_dvd_index_of_le inf_le_left).trans (Subgroup.index_dvd_card _)
    have h2 := Nat.gcd_le_right
      (m := (Subgroup.centralizer P).relindex P.normalizer) ((Nat.card G).minFac - 1)
      (by simp only [tsub_pos_iff_lt, (Nat.minFac_prime hn).one_lt])
    contrapose! h2
    · refine Nat.sub_one_lt_of_le (Nat.card G).minFac_pos ?_
      refine Nat.minFac_le_of_dvd ?_ h1
      rw [Nat.two_le_iff]
      exact ⟨ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h1, h2⟩

theorem thm2 {G : Type*} [Group G] [Finite G] (P : Sylow (Nat.card G).minFac G) (hP : IsCyclic P) :
    (MonoidHom.transferSylow P (thm1 hP)).ker.IsComplement' P := by
  by_cases hn : Nat.card G = 1
  · have := (Nat.card_eq_one_iff_unique.mp hn).1
    rw [Subsingleton.elim (MonoidHom.transferSylow P (thm1 hP)).ker ⊥]
    rw [Subsingleton.elim P.1 ⊤]
    exact Subgroup.isComplement'_bot_top
  have := Fact.mk (Nat.minFac_prime hn)
  exact MonoidHom.ker_transferSylow_isComplement' P (thm1 hP)

end Burnside

namespace IsZGroup

instance [IsZGroup G] : IsSolvable G := by
  -- induction on G, requires Burnside
  sorry

open Monoid in
theorem _root_.IsCyclic.exponent_eq_card' {α : Type*} [Group α] [IsCyclic α] :
    Monoid.exponent α = Nat.card α := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  apply Nat.dvd_antisymm Group.exponent_dvd_nat_card
  rw [← orderOf_generator_eq_natCard hg]
  exact order_dvd_exponent _

theorem exponent_eq_card [IsZGroup G] [Finite G] : Monoid.exponent G = Nat.card G := by
  refine dvd_antisymm Group.exponent_dvd_nat_card ?_
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Monoid.exponent_ne_zero_of_finite]
  intro p hp
  have := Fact.mk hp
  let P : Sylow p G := default
  rw [← hp.pow_dvd_iff_le_factorization Monoid.exponent_ne_zero_of_finite,
      ← P.card_eq_multiplicity, ← (isZGroup p hp P).exponent_eq_card']
  exact Monoid.exponent_dvd_of_monoidHom P.1.subtype P.1.subtype_injective

instance [hG : Group.IsNilpotent G] [IsZGroup G] [Finite G] : IsCyclic G := by
  let h (p : { x // x ∈ (Nat.card G).primeFactors }) (P : Sylow p G) : CommGroup P :=
    have : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    IsCyclic.commGroup
  obtain ⟨ϕ⟩ := ((isNilpotent_of_finite_tfae (G := G)).out 0 4).mp hG
  let _ : CommGroup G :=
    ⟨fun g h ↦ by rw [← ϕ.symm.injective.eq_iff, map_mul, mul_comm, ← map_mul]⟩
  rcases nonempty_fintype (α := G) -- can be removed after merge
  apply IsCyclic.of_exponent_eq_card
  rw [exponent_eq_card, Nat.card_eq_fintype_card]

example [IsZGroup G] [Finite G] : IsCyclic (Abelianization G) := inferInstance

-- If smallest prime divisor is cyclic, then G has normal p-complement (done)
-- ZGroup implies solvable: Induct
-- If p is cyclic, then p cannot divide both |G'| and |G:G'| (prove in generality?)
-- ZGroup implies coprime |G'| and |G:G'|
-- G/G' is cyclic (abelian (or nilpotent) ZGroup is cyclic, directProductOfNormal)
-- G' is cyclic: Theorem 5.16

end IsZGroup

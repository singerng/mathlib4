/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Transfer
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Z Groups



## Main statements


-/

def IsPGroup.toSylow {G : Type*} [Group G] {P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : Sylow p G :=
  { P with
    isPGroup' := hP1
    is_maximal' := by
      intro Q hQ hPQ
      have hP : P.index ≠ 0 := by
        intro h
        rw [h] at hP2
        exact hP2 (dvd_zero p)
      have : P.FiniteIndex := ⟨hP⟩
      let N := P.normalCore
      have : N.FiniteIndex := inferInstance
      have : Q.FiniteIndex := Subgroup.finiteIndex_of_le hPQ
      refine le_antisymm (Subgroup.relindex_eq_one.mp ?_) hPQ
      have key : IsPGroup p (Q ⧸ (N.subgroupOf Q)) := hQ.to_quotient (N.subgroupOf Q)
      obtain ⟨k, hk⟩ := key.exists_card_eq
      rw [← Subgroup.index, ← Subgroup.relindex] at hk
      have h1 : P.relindex Q ∣ N.relindex Q := Subgroup.relindex_dvd_of_le_left Q P.normalCore_le
      have h2 : P.relindex Q ∣ P.index := by exact Subgroup.relindex_dvd_index_of_le hPQ
      rw [hk] at h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp h1
      rw [hj] at h2 ⊢
      cases j
      · rfl
      · rw [pow_succ] at h2
        have key := dvd_of_mul_left_dvd h2
        exact (hP2 key).elim }

theorem IsPGroup.toSylow_coe {G : Type*} [Group G] {P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : (hP1.toSylow hP2) = P :=
  rfl

def Sylow.ofCard' {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G :=
  (IsPGroup.of_card card_eq).toSylow (fun h0 ↦ by
    have key := mul_dvd_mul_left (p ^ (Nat.card G).factorization p) h0
    rw [← pow_succ, ← card_eq, H.card_mul_index, Nat.factorization_def _ Fact.out] at key
    exact pow_succ_padicValNat_not_dvd Nat.card_pos.ne' key)

def Sylow.mapSurjective {G G' : Type*} [Group G] [Finite G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Sylow p G' :=
  { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ ↦ ((P.2.map f).toSylow (fun h ↦ not_dvd_index_sylow P
        (Subgroup.index_ne_zero_of_finite) (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }

theorem Sylow.coe_mapSurjective {G G' : Type*} [Group G] [Finite G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (P.mapSurjective hf : Subgroup G') = P.map f :=
  rfl

theorem Sylow.mapSurjective_surjective {G G' : Type*} [Group G] [Finite G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) (p : ℕ) [Fact p.Prime] :
    Function.Surjective (Sylow.mapSurjective hf : Sylow p G → Sylow p G') := by
  have : Finite G' := Finite.of_surjective f hf
  intro P
  let Q : Sylow p (P.comap f) := Sylow.nonempty.some
  let Q' : Subgroup G := Q.map (P.comap f).subtype
  have hQ' : IsPGroup p Q' := Q.2.map (P.comap f).subtype
  have hQ'' : ¬ p ∣ Q'.index := by
    rw [← Subgroup.relindex_mul_index (Subgroup.map_subtype_le Q.1),
      P.index_comap_of_surjective hf,
      Subgroup.relindex, Subgroup.subgroupOf,
      Q.comap_map_eq_self_of_injective (P.comap f).subtype_injective]
    exact Nat.Prime.not_dvd_mul Fact.out (not_dvd_index_sylow Q (Subgroup.index_ne_zero_of_finite))
      (not_dvd_index_sylow P (Subgroup.index_ne_zero_of_finite))
  refine ⟨hQ'.toSylow hQ'', Sylow.ext ?_⟩
  rw [coe_mapSurjective, IsPGroup.toSylow_coe]
  have hQ''' : ¬ p ∣ (Q'.map f).index :=
    fun h ↦ hQ'' (h.trans (Q'.index_map_dvd hf))
  symm
  apply ((hQ'.map f).toSylow hQ''').3 P.2
  rw [IsPGroup.toSylow_coe, Subgroup.map_le_iff_le_comap]
  exact Subgroup.map_subtype_le Q.1

variable (G G' : Type*) [Group G] [Group G'] (f : G →* G')

class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' f}

theorem IsZGroup_iff : IsZGroup G ↔ ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

namespace IsZGroup

theorem of_injective (hG' : IsZGroup G') (hf : Function.Injective f) : IsZGroup G := by
  rw [IsZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P ≤ Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective

theorem of_surjective [Finite G] (hG' : IsZGroup G) (hf : Function.Surjective f) : IsZGroup G' := by
  rw [IsZGroup_iff] at hG' ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG' p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

-- If smallest prime divisor is cyclic, then G has normal p-complement
-- ZGroup implies solvable: Induct
-- If p is cyclic, then p cannot divide both |G'| and |G:G'|
-- ZGroup implies coprime |G'| and |G:G'|
-- G/G' is cyclic (abelian ZGroup is cyclic)
-- G' is cyclic: Theorem 5.16

end IsZGroup

/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Ring.AddAut
import Mathlib.GroupTheory.Nilpotent
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

section Burnside

def Subgroup.autmap {G : Type*} [Group G] (H : Subgroup G) : H.normalizer →* MulAut H where
  toFun := fun g ↦
    { toFun := fun h ↦ ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
      invFun := fun h ↦ ⟨g⁻¹ * h * g, (mem_normalizer_iff''.mp g.2 h).mp h.2⟩
      left_inv := fun h ↦ by simp [mul_assoc]
      right_inv := fun h ↦ by simp [mul_assoc]
      map_mul' := fun h1 h2 ↦ by simp [mul_assoc] }
  map_one' := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff, mul_assoc]

theorem Subgroup.autmap_ker {G : Type*} [Group G] (H : Subgroup G) :
    H.autmap.ker = (Subgroup.centralizer H).subgroupOf H.normalizer := by
  ext g
  simp [DFunLike.ext_iff, mem_subgroupOf, autmap, mem_centralizer_iff, mul_inv_eq_iff_eq_mul]
  simp [eq_comm]

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
    apply not_dvd_index_sylow P
    exact Nat.card_pos.ne'
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

variable (G G' : Type*) [Group G] [Group G'] (f : G →* G')

class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' f}

theorem IsZGroup_iff : IsZGroup G ↔ ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

namespace IsZGroup

theorem of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G := by
  rw [IsZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P ≤ Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective

theorem of_surjective [Finite G] [hG' : IsZGroup G] (hf : Function.Surjective f) : IsZGroup G' := by
  rw [IsZGroup_iff] at hG' ⊢
  intro p hp P
  have := Fact.mk hp
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective hf p P
  specialize hG' p hp Q
  exact isCyclic_of_surjective _ (f.subgroupMap_surjective Q)

instance [IsZGroup G] (H : Subgroup G) : IsZGroup H := of_injective H.subtype_injective

instance [IsZGroup G] [Finite G] (H : Subgroup G) [H.Normal] : IsZGroup (G ⧸ H) :=
  of_surjective (QuotientGroup.mk'_surjective H)

instance [IsZGroup G] [Finite G] : IsZGroup (Abelianization G) :=
  of_surjective (QuotientGroup.mk'_surjective (commutator G))

instance [Group.IsNilpotent G] [IsZGroup G] : IsCyclic G := sorry

-- this is now automatic!
instance [IsZGroup G] [Finite G] : IsCyclic (Abelianization G) := inferInstance

-- If smallest prime divisor is cyclic, then G has normal p-complement (done)
-- ZGroup implies solvable: Induct
-- If p is cyclic, then p cannot divide both |G'| and |G:G'|
-- ZGroup implies coprime |G'| and |G:G'|
-- G/G' is cyclic (abelian (or nilpotent) ZGroup is cyclic, directProductOfNormal)
-- G' is cyclic: Theorem 5.16

end IsZGroup

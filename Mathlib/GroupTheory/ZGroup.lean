/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Transfer

/-!
# Z Groups



## Main statements


-/

def Sylow.mapSurjective {G G' : Type*} [Group G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} (P : Sylow p G) : Sylow p G' :=
  { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := by

      sorry }

theorem Sylow.coe_mapSurjective {G G' : Type*} [Group G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) {p : ℕ} (P : Sylow p G) :
    (P.mapSurjective hf : Subgroup G') = P.map f :=
  rfl

theorem Sylow.mapSurjective_surjective {G G' : Type*} [Group G] [Group G']
    {f : G →* G'} (hf : Function.Surjective f) (p : ℕ) :
    Function.Surjective (Sylow.mapSurjective hf : Sylow p G → Sylow p G') := by
  sorry

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

theorem of_surjective (hG' : IsZGroup G) (hf : Function.Surjective f) : IsZGroup G' := by
  rw [IsZGroup_iff] at hG' ⊢
  intro p hp P
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

/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
import Mathlib.Algebra.Ring.Int
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Coxeter groups and Coxeter systems

This file defines Coxeter groups and Coxeter systems.

Let `B` be a (possibly infinite) type, and let $M = (M_{i,i'})_{i, i' \in B}$ be a matrix
of natural numbers. Further assume that $M$ is a *Coxeter matrix* (`CoxeterMatrix`); that is, $M$ is
symmetric and $M_{i,i'} = 1$ if and only if $i = i'$. The *Coxeter group* associated to $M$
(`CoxeterMatrix.group`) has the presentation
$$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$
The elements $s_i$ are called the *simple reflections* (`CoxeterMatrix.simple`) of the Coxeter
group. Note that every simple reflection is an involution.

A *Coxeter system* (`CoxeterSystem`) is a group $W$, together with an isomorphism between $W$ and
the Coxeter group associated to some Coxeter matrix $M$. By abuse of language, we also say that $W$
is a Coxeter group (`IsCoxeterGroup`), and we may speak of the simple reflections $s_i \in W$
(`CoxeterSystem.simple`). We state all of our results about Coxeter groups in terms of Coxeter
systems where possible.

Let $W$ be a group equipped with a Coxeter system. For all monoids $G$ and all functions
$f \colon B \to G$ whose values satisfy the Coxeter relations, we may lift $f$ to a multiplicative
homomorphism $W \to G$ (`CoxeterSystem.lift`) in a unique way.

A *word* is a sequence of elements of $B$. The word $(i_1, \ldots, i_\ell)$ has a corresponding
product $s_{i_1} \cdots s_{i_\ell} \in W$ (`CoxeterSystem.wordProd`). Every element of $W$ is the
product of some word (`CoxeterSystem.wordProd_surjective`). The words that alternate between two
elements of $B$ (`CoxeterSystem.alternatingWord`) are particularly important.

## Implementation details

Much of the literature on Coxeter groups conflates the set $S = \{s_i : i \in B\} \subseteq W$ of
simple reflections with the set $B$ that indexes the simple reflections. This is usually permissible
because the simple reflections $s_i$ of any Coxeter group are all distinct (a nontrivial fact that
we do not prove in this file). In contrast, we try not to refer to the set $S$ of simple
reflections unless necessary; instead, we state our results in terms of $B$ wherever possible.

## Main definitions

* `CoxeterMatrix.Group`
* `CoxeterSystem`
* `IsCoxeterGroup`
* `CoxeterSystem.simple` : If `cs` is a Coxeter system on the group `W`, then `cs.simple i` is the
  simple reflection of `W` at the index `i`.
* `CoxeterSystem.lift` : Extend a function `f : B → G` to a monoid homomorphism `f' : W → G`
  satisfying `f' (cs.simple i) = f i` for all `i`.
* `CoxeterSystem.wordProd`
* `CoxeterSystem.alternatingWord`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

## TODO

* The simple reflections of a Coxeter system are distinct.
* Introduce some ways to actually construct some Coxeter groups. For example, given a Coxeter matrix
$M : B \times B \to \mathbb{N}$, a real vector space $V$, a basis $\{\alpha_i : i \in B\}$
and a bilinear form $\langle \cdot, \cdot \rangle \colon V \times V \to \mathbb{R}$ satisfying
$$\langle \alpha_i, \alpha_{i'}\rangle = - \cos(\pi / M_{i,i'}),$$ one can form the subgroup of
$GL(V)$ generated by the reflections in the $\alpha_i$, and it is a Coxeter group. We can use this
to combinatorially describe the Coxeter groups of type $A$, $B$, $D$, and $I$.
* State and prove Matsumoto's theorem.
* Classify the finite Coxeter groups.

## Tags

coxeter system, coxeter group

-/

open Function Set List

/-! ### Coxeter groups -/

namespace CoxeterMatrix

variable {B B' : Type*} (M : CoxeterMatrix B) (e : B ≃ B')

/-- The Coxeter relation associated to a Coxeter matrix $M$ and two indices $i, i' \in B$.
That is, the relation $(s_i s_{i'})^{M_{i, i'}}$, considered as an element of the free group
on $\{s_i\}_{i \in B}$.
If $M_{i, i'} = 0$, then this is the identity, indicating that there is no relation between
$s_i$ and $s_{i'}$. -/
def relation (i i' : B) : FreeGroup B := (FreeGroup.of i * FreeGroup.of i') ^ M i i'

/-- The set of all Coxeter relations associated to the Coxeter matrix $M$. -/
def relationsSet : Set (FreeGroup B) := range <| uncurry M.relation

/-- The Coxeter group associated to a Coxeter matrix $M$; that is, the group
$$\langle \{s_i\}_{i \in B} \vert \{(s_i s_{i'})^{M_{i, i'}}\}_{i, i' \in B} \rangle.$$ -/
protected def Group : Type _ := PresentedGroup M.relationsSet

instance : Group M.Group := QuotientGroup.Quotient.group _

/-- The simple reflection of the Coxeter group `M.group` at the index `i`. -/
def simple (i : B) : M.Group := PresentedGroup.of i

theorem reindex_relationsSet :
    (M.reindex e).relationsSet =
    FreeGroup.freeGroupCongr e '' M.relationsSet := let M' := M.reindex e; calc
  Set.range (uncurry M'.relation)
  _ = Set.range (uncurry M'.relation ∘ Prod.map e e) := by simp [Set.range_comp]
  _ = Set.range (FreeGroup.freeGroupCongr e ∘ uncurry M.relation) := by
      apply congrArg Set.range
      ext ⟨i, i'⟩
      simp [relation, reindex_apply, M']
  _ = _ := by simp [Set.range_comp, relationsSet]

/-- The isomorphism between the Coxeter group associated to the reindexed matrix `M.reindex e` and
the Coxeter group associated to `M`. -/
def reindexGroupEquiv : (M.reindex e).Group ≃* M.Group :=
  .symm <| QuotientGroup.congr
    (Subgroup.normalClosure M.relationsSet)
    (Subgroup.normalClosure (M.reindex e).relationsSet)
    (FreeGroup.freeGroupCongr e)
    (by
      rw [reindex_relationsSet,
        Subgroup.map_normalClosure _ _ (by simpa using (FreeGroup.freeGroupCongr e).surjective),
        MonoidHom.coe_coe])

theorem reindexGroupEquiv_apply_simple (i : B') :
    (M.reindexGroupEquiv e) ((M.reindex e).simple i) = M.simple (e.symm i) := rfl

theorem reindexGroupEquiv_symm_apply_simple (i : B) :
    (M.reindexGroupEquiv e).symm (M.simple i) = (M.reindex e).simple (e i) := rfl

end CoxeterMatrix

/-! ### Coxeter systems -/

section

variable {B : Type*} (M : CoxeterMatrix B)

/-- A Coxeter system `CoxeterSystem M W` is a structure recording the isomorphism between
a group `W` and the Coxeter group associated to a Coxeter matrix `M`. -/
@[ext]
structure CoxeterSystem (W : Type*) [Group W] where
  /-- The isomorphism between `W` and the Coxeter group associated to `M`. -/
  mulEquiv : W ≃* M.Group

/-- A group is a Coxeter group if it admits a Coxeter system for some Coxeter matrix `M`. -/
class IsCoxeterGroup.{u} (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ B : Type u, ∃ M : CoxeterMatrix B, Nonempty (CoxeterSystem M W)

/-- The canonical Coxeter system on the Coxeter group associated to `M`. -/
def CoxeterMatrix.toCoxeterSystem : CoxeterSystem M M.Group := ⟨.refl _⟩

end

namespace CoxeterSystem

open CoxeterMatrix

variable {B B' : Type*} (e : B ≃ B')
variable {W H : Type*} [Group W] [Group H]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Reindex a Coxeter system through a bijection of the indexing sets. -/
@[simps]
protected def reindex (e : B ≃ B') : CoxeterSystem (M.reindex e) W :=
  ⟨cs.mulEquiv.trans (M.reindexGroupEquiv e).symm⟩

/-- Push a Coxeter system through a group isomorphism. -/
@[simps]
protected def map (e : W ≃* H) : CoxeterSystem M H := ⟨e.symm.trans cs.mulEquiv⟩

/-! ### Simple reflections -/

/-- The simple reflection of `W` at the index `i`. -/
def simple (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)

@[simp]
theorem _root_.CoxeterMatrix.toCoxeterSystem_simple (M : CoxeterMatrix B) :
    M.toCoxeterSystem.simple = M.simple := rfl

@[simp] theorem reindex_simple (i' : B') : (cs.reindex e).simple i' = cs.simple (e.symm i') := rfl

@[simp] theorem map_simple (e : W ≃* H) (i : B) : (cs.map e).simple i = e (cs.simple i) := rfl

local prefix:100 "s" => cs.simple

@[simp]
theorem simple_mul_simple_self (i : B) : s i * s i = 1 := by
  have : (FreeGroup.of i) * (FreeGroup.of i) ∈ M.relationsSet := ⟨(i, i), by simp [relation]⟩
  have : (QuotientGroup.mk (FreeGroup.of i * FreeGroup.of i) : M.Group) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure this)
  unfold simple
  rw [← map_mul, PresentedGroup.of, ← QuotientGroup.mk_mul, this, map_one]

@[simp]
theorem simple_mul_simple_cancel_right {w : W} (i : B) : w * s i * s i = w := by
  simp [mul_assoc]

@[simp]
theorem simple_mul_simple_cancel_left {w : W} (i : B) : s i * (s i * w) = w := by
  simp [← mul_assoc]

@[simp] theorem simple_sq (i : B) : s i ^ 2 = 1 := pow_two (s i) ▸ cs.simple_mul_simple_self i

@[simp]
theorem inv_simple (i : B) : (s i)⁻¹ = s i :=
  (eq_inv_of_mul_eq_one_right (cs.simple_mul_simple_self i)).symm

@[simp]
theorem simple_mul_simple_pow (i i' : B) : (s i * s i') ^ M i i' = 1 := by
  have : (FreeGroup.of i * FreeGroup.of i') ^ M i i' ∈ M.relationsSet := ⟨(i, i'), rfl⟩
  have : (QuotientGroup.mk ((FreeGroup.of i * FreeGroup.of i') ^ M i i') : M.Group) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure this)
  unfold simple
  rw [← map_mul, ← map_pow, PresentedGroup.of, PresentedGroup.of,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, this, map_one]

@[simp] theorem simple_mul_simple_pow' (i i' : B) : (s i' * s i) ^ M i i' = 1 :=
  M.symmetric i' i ▸ cs.simple_mul_simple_pow i' i

/-- The simple reflections of `W` generate `W` as a group. -/
theorem subgroup_closure_range_simple : Subgroup.closure (range cs.simple) = ⊤ := by
  have : cs.simple = cs.mulEquiv.symm ∘ PresentedGroup.of := rfl
  rw [this, Set.range_comp, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure,
    PresentedGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_top_of_surjective _ (MulEquiv.surjective _)

/-- The simple reflections of `W` generate `W` as a monoid. -/
theorem submonoid_closure_range_simple : Submonoid.closure (range cs.simple) = ⊤ := by
  have : range cs.simple = range cs.simple ∪ (range cs.simple)⁻¹ := by
    simp_rw [inv_range, inv_simple, union_self]
  rw [this, ← Subgroup.closure_toSubmonoid, subgroup_closure_range_simple, Subgroup.top_toSubmonoid]

/-! ### Induction principles for Coxeter systems -/

/-- If `p : W → Prop` holds for all simple reflections, it holds for the identity, and it is
preserved under multiplication, then it holds for all elements of `W`. -/
theorem simple_induction {p : W → Prop} (w : W) (simple : ∀ i : B, p (s i)) (one : p 1)
    (mul : ∀ w w' : W, p w → p w' → p (w * w')) : p w := by
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  exact Submonoid.closure_induction this (fun x ⟨i, hi⟩ ↦ hi ▸ simple i) one mul

/-- If `p : W → Prop` holds for the identity and it is preserved under multiplying on the left
by a simple reflection, then it holds for all elements of `W`. -/
theorem simple_induction_left {p : W → Prop} (w : W) (one : p 1)
    (mul_simple_left : ∀ (w : W) (i : B), p w → p (s i * w)) : p w := by
  let p' : (w : W) → w ∈ Submonoid.closure (Set.range cs.simple) → Prop :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction_left (p := p')
  · exact one
  · rintro _ ⟨i, rfl⟩ y _
    exact mul_simple_left y i
  · exact this

/-- If `p : W → Prop` holds for the identity and it is preserved under multiplying on the right
by a simple reflection, then it holds for all elements of `W`. -/
theorem simple_induction_right {p : W → Prop} (w : W) (one : p 1)
    (mul_simple_right : ∀ (w : W) (i : B), p w → p (w * s i)) : p w := by
  let p' : ((w : W) → w ∈ Submonoid.closure (Set.range cs.simple) → Prop) :=
    fun w _ ↦ p w
  have := cs.submonoid_closure_range_simple.symm ▸ Submonoid.mem_top w
  apply Submonoid.closure_induction_right (p := p')
  · exact one
  · rintro x _ _ ⟨i, rfl⟩
    exact mul_simple_right x i
  · exact this

/-! ### Homomorphisms from a Coxeter group -/

/-- If two homomorphisms with domain `W` agree on all simple reflections, then they are equal. -/
theorem ext_simple {G : Type*} [Monoid G] {φ₁ φ₂ : W →* G} (h : ∀ i : B, φ₁ (s i) = φ₂ (s i)) :
    φ₁ = φ₂ :=
  MonoidHom.eq_of_eqOn_denseM cs.submonoid_closure_range_simple (fun _ ⟨i, hi⟩ ↦ hi ▸ h i)

/-- The proposition that the values of the function `f : B → G` satisfy the Coxeter relations
corresponding to the matrix `M`. -/
def _root_.CoxeterMatrix.IsLiftable {G : Type*} [Monoid G] (M : CoxeterMatrix B) (f : B → G) :
    Prop := ∀ i i', (f i * f i') ^ M i i' = 1

private theorem relations_liftable {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f)
    (r : FreeGroup B) (hr : r ∈ M.relationsSet) : (FreeGroup.lift f) r = 1 := by
  rcases hr with ⟨⟨i, i'⟩, rfl⟩
  rw [uncurry, relation, map_pow, _root_.map_mul, FreeGroup.lift.of, FreeGroup.lift.of]
  exact hf i i'

private def groupLift {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  (PresentedGroup.toGroup (relations_liftable hf)).comp cs.mulEquiv.toMonoidHom

private def restrictUnit {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    Gˣ where
  val := f i
  inv := f i
  val_inv := pow_one (f i * f i) ▸ M.diagonal i ▸ hf i i
  inv_val := pow_one (f i * f i) ▸ M.diagonal i ▸ hf i i

private theorem toMonoidHom_apply_symm_apply (a : PresentedGroup (M.relationsSet)) :
    (MulEquiv.toMonoidHom cs.mulEquiv : W →* PresentedGroup (M.relationsSet))
    ((MulEquiv.symm cs.mulEquiv) a) = a := calc
  _ = cs.mulEquiv ((MulEquiv.symm cs.mulEquiv) a) := by rfl
  _ = _                                           := by rw [MulEquiv.apply_symm_apply]

/-- The universal mapping property of Coxeter systems. For any monoid `G`,
functions `f : B → G` whose values satisfy the Coxeter relations are equivalent to
monoid homomorphisms `f' : W → G`. -/
def lift {G : Type*} [Monoid G] : {f : B → G // IsLiftable M f} ≃ (W →* G) where
  toFun f := MonoidHom.comp (Units.coeHom G) (cs.groupLift
    (show ∀ i i', ((restrictUnit f.property) i * (restrictUnit f.property) i') ^ M i i' = 1 from
      fun i i' ↦ Units.ext (f.property i i')))
  invFun ι := ⟨ι ∘ cs.simple, fun i i' ↦ by
    rw [comp_apply, comp_apply, ← map_mul, ← map_pow, simple_mul_simple_pow, map_one]⟩
  left_inv f := by
    ext i
    simp only [MonoidHom.comp_apply, comp_apply, mem_setOf_eq, groupLift, simple]
    rw [← MonoidHom.toFun_eq_coe, toMonoidHom_apply_symm_apply, PresentedGroup.toGroup.of,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Units.coeHom_apply, restrictUnit]
  right_inv ι := by
    apply cs.ext_simple
    intro i
    dsimp only
    rw [groupLift, simple, MonoidHom.comp_apply, MonoidHom.comp_apply, toMonoidHom_apply_symm_apply,
      PresentedGroup.toGroup.of, CoxeterSystem.restrictUnit, Units.coeHom_apply]
    simp only [comp_apply, simple]

@[simp]
theorem lift_apply_simple {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) (i : B) :
    cs.lift ⟨f, hf⟩ (s i) = f i := congrFun (congrArg Subtype.val (cs.lift.left_inv ⟨f, hf⟩)) i

/-- If two Coxeter systems on the same group `W` have the same Coxeter matrix `M : Matrix B B ℕ`
and the same simple reflection map `B → W`, then they are identical. -/
theorem simple_determines_coxeterSystem :
    Injective (simple : CoxeterSystem M W → B → W) := by
  intro cs1 cs2 h
  apply CoxeterSystem.ext
  apply MulEquiv.toMonoidHom_injective
  apply cs1.ext_simple
  intro i
  nth_rw 2 [h]
  simp [simple]

/-! ### Words -/

/-- The product of the simple reflections of `W` corresponding to the indices in `ω`. -/
def wordProd (ω : List B) : W := prod (map cs.simple ω)

local prefix:100 "π" => cs.wordProd

@[simp] theorem wordProd_nil : π [] = 1 := by simp [wordProd]

theorem wordProd_cons (i : B) (ω : List B) : π (i :: ω) = s i * π ω := by simp [wordProd]

@[simp] theorem wordProd_singleton (i : B) : π ([i]) = s i := by simp [wordProd]

theorem wordProd_concat (i : B) (ω : List B) : π (ω.concat i) = π ω * s i := by simp [wordProd]

theorem wordProd_append (ω ω' : List B) : π (ω ++ ω') = π ω * π ω' := by simp [wordProd]

@[simp] theorem wordProd_reverse (ω : List B) : π (reverse ω) = (π ω)⁻¹ := by
  induction' ω with x ω' ih
  · simp
  · simpa [wordProd_cons, wordProd_append] using ih

theorem wordProd_surjective : Surjective cs.wordProd := by
  intro w
  apply cs.simple_induction_left w
  · use []
    rw [wordProd_nil]
  · rintro _ i ⟨ω, rfl⟩
    use i :: ω
    rw [wordProd_cons]

/-- The word of length `m` that alternates between `i` and `i'`, ending with `i'`. -/
def alternatingWord (i i' : B) (m : ℕ) : List B :=
  match m with
  | 0    => []
  | m+1  => (alternatingWord i' i m).concat i'

/-- The word of length `M i i'` that alternates between `i` and `i'`, ending with `i'`. -/
abbrev braidWord (M : CoxeterMatrix B) (i i' : B) : List B := alternatingWord i i' (M i i')

theorem alternatingWord_succ (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (alternatingWord i' i m).concat i' := rfl

theorem alternatingWord_succ' (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (if Even m then i' else i) :: alternatingWord i i' m := by
  induction' m with m ih generalizing i i'
  · simp [alternatingWord]
  · rw [alternatingWord]
    nth_rw 1 [ih i' i]
    rw [alternatingWord]
    simp [Nat.even_add_one]

@[simp]
theorem length_alternatingWord (i i' : B) (m : ℕ) :
    List.length (alternatingWord i i' m) = m := by
  induction' m with m ih generalizing i i'
  · dsimp [alternatingWord]
  · simpa [alternatingWord] using ih i' i

theorem prod_alternatingWord_eq_mul_pow (i i' : B) (m : ℕ) :
    π (alternatingWord i i' m) = (if Even m then 1 else s i') * (s i * s i') ^ (m / 2) := by
  induction' m with m ih
  · simp [alternatingWord]
  · rw [alternatingWord_succ', wordProd_cons, ih]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
      simp [hm, h₁, h₂]
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
      simp [hm, h₁, h₂, ← pow_succ', ← mul_assoc]

theorem prod_alternatingWord_eq_prod_alternatingWord_sub (i i' : B) (m : ℕ) (hm : m ≤ M i i' * 2) :
    π (alternatingWord i i' m) = π (alternatingWord i' i (M i i' * 2 - m)) := by
  simp_rw [prod_alternatingWord_eq_mul_pow, ← Int.even_coe_nat]

  /- Rewrite everything in terms of an integer m' which is equal to m.
  The resulting equation holds for all integers m'. -/
  simp_rw [← zpow_natCast, Int.ofNat_ediv, Int.ofNat_sub hm]
  generalize (m : ℤ) = m'
  clear hm
  push_cast

  rcases Int.even_or_odd' m' with ⟨k, rfl | rfl⟩
  · rw [if_pos (by use k; ring), if_pos (by use -k + (M i i'); ring), mul_comm 2 k, ← sub_mul]
    repeat rw [Int.mul_ediv_cancel _ (by norm_num)]
    rw [zpow_sub, zpow_natCast, simple_mul_simple_pow' cs i i', ← inv_zpow]
    simp
  · have : ¬Even (2 * k + 1) := Int.odd_iff_not_even.mp ⟨k, rfl⟩
    rw [if_neg this]
    have : ¬Even (↑(M i i') * 2 - (2 * k + 1)) :=
      Int.odd_iff_not_even.mp ⟨↑(M i i') - k - 1, by ring⟩
    rw [if_neg this]

    rw [(by ring : ↑(M i i') * 2 - (2 * k + 1) = -1 + (-k + ↑(M i i')) * 2),
      (by ring : 2 * k + 1 = 1 + k * 2)]
    repeat rw [Int.add_mul_ediv_right _ _ (by norm_num)]
    norm_num

    rw [zpow_add, zpow_add, zpow_natCast, simple_mul_simple_pow', zpow_neg, ← inv_zpow, zpow_neg,
      ← inv_zpow]
    simp [← mul_assoc]

/-- The two words of length `M i i'` that alternate between `i` and `i'` have the same product.
This is known as the "braid relation" or "Artin-Tits relation". -/
theorem wordProd_braidWord_eq (i i' : B) :
    π (braidWord M i i') = π (braidWord M i' i) := by
  have := cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' (M i i')
    (Nat.le_mul_of_pos_right _ (by norm_num))
  rw [tsub_eq_of_eq_add (mul_two (M i i'))] at this
  nth_rw 2 [M.symmetric i i'] at this
  exact this

end CoxeterSystem

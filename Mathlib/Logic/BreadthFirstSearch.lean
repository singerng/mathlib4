/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Fintype.Basic

/-!
# Breadth-first search of a relation

In this file we define breadth-first search of a decidable relation over a finite type with
decidable equality. We define two versions, both returning the elements at a specified depth:
* `bfsReflTrans`, which confers reflexibility on the given relation and computes
  `Relation.ReflTransGen r`
* `bfsTrans`, which does not and computes `Relation.TransGen r`
-/

open Finset List

variable {α : Type*} [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- Helper function for `bfsReflTrans` and `bfsTrans`. Given a pair of finsets `(p, q)`,
computes the set `k` of elements in `q` related to some element in `p` and returns `(k, q \ k)`.

`p` may be thought of as the frontier of the breadth-first search and `q` the unexplored nodes. -/
def bfsAux (p : Finset α × Finset α) : Finset α × Finset α :=
  let k := p.2.filter (fun b ↦ ∃ a ∈ p.1, r a b)
  (k, p.2 \ k)

section BFSAux

variable {r}
variable {p : Finset α × Finset α}

lemma disjoint_bfsAux : Disjoint (bfsAux r p).1 (bfsAux r p).2 := disjoint_sdiff

lemma bfsAux_union_bfsAux : (bfsAux r p).1 ∪ (bfsAux r p).2 = p.2 :=
  union_sdiff_of_subset (filter_subset ..)

lemma mem_fst_bfsAux_iff {b : α} : b ∈ (bfsAux r p).1 ↔ b ∈ p.2 ∧ ∃ a ∈ p.1, r a b := by
  rw [bfsAux, Finset.mem_filter]

lemma exists_of_mem_fst_iterate_bfsAux {b : α} {d : ℕ} (hb : b ∈ ((bfsAux r)^[d] p).1) :
    ∃ a ∈ p.1, ∃ l : List α, l.length = d ∧ Chain r a l ∧
      (a :: l).getLast (cons_ne_nil _ _) = b := by
  induction d generalizing b with
  | zero => use b, by simp_all, []; simp_all
  | succ d ih =>
    rw [Function.iterate_succ_apply', mem_fst_bfsAux_iff] at hb
    obtain ⟨_, a', ma', ra'⟩ := hb
    obtain ⟨a, a_mem, l, l_len, l_chain, l_last⟩ := ih ma'
    refine ⟨a, a_mem, l.concat b, by simp [l_len], ?_, by simp⟩
    rw [concat_eq_append, chain_append_singleton, l_last]; tauto

end BFSAux

variable [Fintype α] (roots : Finset α)

/-- Elements at distance `d` from the given set of roots, assuming reflexivity in addition. -/
def bfsReflTrans (d : ℕ) : Finset α := ((bfsAux r)^[d] (roots, rootsᶜ)).1

/-- Elements at distance `d` from the given set of roots, _not_ assuming reflexivity. -/
def bfsTrans (d : ℕ) : Finset α := ((bfsAux r)^[d] (roots, univ)).1

variable {roots}
variable {d : ℕ}

@[simp] lemma bfsReflTrans_zero : bfsReflTrans r roots 0 = roots := rfl
@[simp] lemma bfsTrans_zero : bfsTrans r roots 0 = roots := rfl

-- instance bleh : DecidableRel (Relation.TransGen r) := by infer_instance

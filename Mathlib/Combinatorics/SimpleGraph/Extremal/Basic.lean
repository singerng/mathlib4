/-
Copyright (c) 2024 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Extremal graph theory

This modules defines the basic definitions of extremal graph theory, including extremal numbers.

## Main definitions

* `SimpleGraph.SubgraphIso A B`, `A ≲g B` is the type of subgraph isomorphisms from `A` to `B`,
  implemented as the subtype of *injective* homomorphisms.

  It is standard to define a subgraph isomorphism as an isomorphism from `A` to a subgraph of `B`.
  However, `SimpleGraph.IsSubgraph` is such that subgraphs of `B` have the same number of vertices
  as `B`. In this case, it is impossible to have a subgraph isomorphism from `A` to `B` using
  `SimpleGraph.IsSubgraph` unless `A` and `B` have the same number of vertices. It is for this
  reason that the mathematically equivalent definition of a subgraph isomorphism as an *injective*
  homomorphism is taken.

* `SimpleGraph.IsIsoSubgraph` is the relation that `B` contains a copy of `A`, that
  is, `A` is an isomorphic subgraph of `B`, that is, the type of subgraph isomorphisms from `A` to
  `B` is nonempty.

  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.

* `SimpleGraph.Free` is the predicate that `B` is `A`-free, that is, `B` does not contain a copy of
  `A`. This is the negation of `SimpleGraph.IsIsoSubgraph` implemented for convenience.

* `SimpleGraph.extremalNumber` is the maximum number of edges in a `A`-free simple graph on the
  vertex type `β`.

  If `A` is contained in all simple graphs on the vertex type `β`, then this is `0`.

* `SimpleGraph.IsExtremal` is the predicate that `G` satisfies `p` and any `H` satisfying `p` has
  at most as many edges as `G`.
-/


namespace SimpleGraph

variable {V α β γ : Type*} {G : SimpleGraph V}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

section SubgraphIso

/-- The type of subgraph isomorphisms as a subtype of *injective* homomorphisms.

The notation `A ≲g B` is introduced for the type of subgrah isomorphisms. -/
abbrev SubgraphIso (A : SimpleGraph α) (B : SimpleGraph β) :=
  { f : A →g B // Function.Injective f }

@[inherit_doc] infixl:50 " ≲g " => SubgraphIso

/-- An injective homomorphism gives rise to a subgraph isomorphism. -/
abbrev Hom.toSubgraphIso (f : A →g B) (h : Function.Injective f) : A ≲g B := ⟨f, h⟩

/-- An embedding gives rise to a subgraph isomorphism. -/
abbrev Embedding.toSubgraphIso (f : A ↪g B) : A ≲g B := Hom.toSubgraphIso f.toHom f.injective

/-- An isomorphism gives rise to a subgraph isomorphism. -/
abbrev Iso.toSubgraphIso (f : A ≃g B) : A ≲g B := Embedding.toSubgraphIso f.toEmbedding

namespace SubgraphIso

/-- A subgraph isomorphism gives rise to a homomorphism. -/
abbrev toHom : A ≲g B → A →g B := Subtype.val

@[simp] lemma coe_toHom (f : A ≲g B) : ⇑f.toHom = f := rfl

abbrev injective : (f : A ≲g B) → (Function.Injective f.toHom) := Subtype.prop

instance : FunLike (A ≲g B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective' _ _ h := Subtype.val_injective (DFunLike.coe_injective h)

/-- A subgraph isomorphism induces an embedding of edge sets. -/
def mapEdgeSet (f : A ≲g B) : A.edgeSet ↪ B.edgeSet where
  toFun := Hom.mapEdgeSet f.toHom
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A subgraph isomorphisms induces an embedding of neighbor sets. -/
def mapNeighborSet (f : A ≲g B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

instance : EmbeddingLike (A ≲g B) α β where
  injective' f := f.injective

/-- A subgraph isomorphism gives rise to embeddings of vertex types. -/
def asEmbedding (f : A ≲g B) : α ↪ β := ⟨f, EmbeddingLike.injective f⟩

/-- The identity subgraph isomorphism from a simple graph to itself. -/
@[refl] def refl (G : SimpleGraph V) : G ≲g G := ⟨Hom.id, Function.injective_id⟩

/-- The subgraph isomorphism from a subgraph to the supergraph. -/
def ofLE {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) : G₁ ≲g G₂ :=
  ⟨Hom.ofLE h, Function.injective_id⟩

/-- The subgraph isomorphism from an induced subgraph to the initial simple graph. -/
def induce (G : SimpleGraph V) (s : Set V) : (G.induce s) ≲g G :=
  (Embedding.induce s).toSubgraphIso

/-- The composition of subgraph isomorphisms is a subgraph isomorphism. -/
def comp (g : B ≲g C) (f : A ≲g B) : A ≲g C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact Function.Injective.comp g.injective f.injective

theorem comp_apply (g : B ≲g C) (f : A ≲g B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

end SubgraphIso

end SubgraphIso

end SimpleGraph

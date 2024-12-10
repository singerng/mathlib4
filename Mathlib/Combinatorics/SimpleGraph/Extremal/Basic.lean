/-
Copyright (c) 2024 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/

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

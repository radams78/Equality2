module Semantics.RefGraph where
open import Level

-- A reflexive graph is a multigraph where every vertex has a path to itself
record RefGraph i j : Set (suc (i ⊔ j)) where
  field
    Vertex  : Set i
    Path    : Vertex → Vertex → Set j
    ref     : ∀ x → Path x x

  record Square : Set (i ⊔ j) where
    field
      nw : Vertex
      ne : Vertex
      sw : Vertex
      se : Vertex
      north : Path nw ne
      south : Path sw se
      west  : Path nw sw
      east  : Path ne se

module RefGraphFunctors {i i' j j'} (S : RefGraph i j) (T : RefGraph i' j') where

  data RefGraphFunctor : Set (i ⊔ i' ⊔ j ⊔ j') where
    mkRefGraphFunctor : ∀
      (ap-vertex : RefGraph.Vertex S → RefGraph.Vertex T)
      (ap-path : ∀ {x y} → RefGraph.Path S x y → RefGraph.Path T (ap-vertex x) (ap-vertex y)) →
      RefGraphFunctor

  ap-vertex : RefGraphFunctor → RefGraph.Vertex S → RefGraph.Vertex T
  ap-vertex (mkRefGraphFunctor ap-vertex _) = ap-vertex

  ap-path : ∀ (F : RefGraphFunctor) {x y} → RefGraph.Path S x y → RefGraph.Path T (ap-vertex F x) (ap-vertex F y)
  ap-path (mkRefGraphFunctor _ ap-path) = ap-path

  ap-square : RefGraphFunctor → RefGraph.Square S → RefGraph.Square T
  ap-square F sq = record
                { nw = ap-vertex F (RefGraph.Square.nw sq)
                ; ne = ap-vertex F (RefGraph.Square.ne sq)
                ; sw = ap-vertex F (RefGraph.Square.sw sq)
                ; se = ap-vertex F (RefGraph.Square.se sq)
                ; north = ap-path F (RefGraph.Square.north sq)
                ; south = ap-path F (RefGraph.Square.south sq)
                ; west = ap-path F (RefGraph.Square.west sq)
                ; east = ap-path F (RefGraph.Square.east sq)
                }

open RefGraphFunctors public

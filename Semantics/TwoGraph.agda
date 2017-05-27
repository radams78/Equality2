{-# OPTIONS --rewriting #-}
module Semantics.TwoGraph where
open import Level
open import Semantics.RefGraph hiding (ap-vertex;ap-path;ap-square)

postulate _▷_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}

-- A 2-graph is a reflexive graph together with, for every square, a set of
-- fillings of that square.
record IsTwoGraph {i} {j} (G : RefGraph i j) k : Set (i ⊔ j ⊔ suc k) where
  open RefGraph G
  field
    Fill : Square → Set k

record TwoGraph i j k : Set (suc (i ⊔ j ⊔ k)) where
  field
    graph : RefGraph i j
    isTwoGraph : IsTwoGraph graph k

  open RefGraph graph public
  open IsTwoGraph isTwoGraph public

data TwoGraphFunctor {i i' j j' k k'} (S : TwoGraph i j k) (T : TwoGraph i' j' k') : Set (i ⊔ i' ⊔ j ⊔ j' ⊔ k ⊔ k') where
  mkTwoGraphFunctor :
    ∀ (graphFunctor : RefGraphFunctor (TwoGraph.graph S) (TwoGraph.graph T)) →
    (∀ {sq} → TwoGraph.Fill S sq → TwoGraph.Fill T (Semantics.RefGraph.ap-square _ _ graphFunctor sq)) →
    TwoGraphFunctor S T

ap-vertex : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'} →
  TwoGraphFunctor S T → TwoGraph.Vertex S → TwoGraph.Vertex T
ap-vertex (mkTwoGraphFunctor refGraphFunctor _) = Semantics.RefGraph.ap-vertex _ _ refGraphFunctor

ap-path : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
  (F : TwoGraphFunctor S T) {x y} → TwoGraph.Path S x y → TwoGraph.Path T (ap-vertex F x) (ap-vertex F y)
ap-path (mkTwoGraphFunctor (mkRefGraphFunctor _ ap-path) _) = ap-path

postulate ap-path-ref : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
                   (F : TwoGraphFunctor S T) (x : TwoGraph.Vertex S) →
                   ap-path F (TwoGraph.ref S x) ▷ TwoGraph.ref T (ap-vertex F x)
{-# REWRITE ap-path-ref #-}

ap-square : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
  (F : TwoGraphFunctor S T) → TwoGraph.Square S → TwoGraph.Square T
ap-square (mkTwoGraphFunctor refGraphFunctor _) = Semantics.RefGraph.ap-square _ _ refGraphFunctor

ap-fill : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
  (F : TwoGraphFunctor S T) {sq} → TwoGraph.Fill S sq → TwoGraph.Fill T (ap-square F sq)
ap-fill (mkTwoGraphFunctor _ isTwoGraphFunctor) = isTwoGraphFunctor


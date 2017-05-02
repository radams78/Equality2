{-# OPTIONS --rewriting #-}
module FibSetoid where
open import Level

postulate _▷_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}

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

-- A 2-graph is a reflexive graph together with, for every square, a set of
-- fillings of that square.
  record IsTwoGraph k : Set (i ⊔ j ⊔ suc k) where
    field
      Fill : Square → Set k

record TwoGraph i j k : Set (suc (i ⊔ j ⊔ k)) where
  field
    graph : RefGraph i j
    isTwoGraph : RefGraph.IsTwoGraph graph k

  open RefGraph graph public
  open IsTwoGraph isTwoGraph public

-- A universe consists of:
-- * a set of (names of) types
-- * for any type A, a set of elements of A
-- * for any types A B, a type A = B
-- * for any a : A, p : A = B and b : B, a set a ~< p > b of paths from a to b over p
-- * for any A, an element ref A : A = A
-- * for any p : A = A' and q : B = B', an element p =* q : (A = B) = (A' = B')
record FibSetoid i j k : Set (suc (i ⊔ j ⊔ k)) where
  field
    Dom  : Set i
    Fib  : Dom → Set j
    eqG  : Dom → Dom → Dom
    ref  : ∀ A → Fib (eqG A A)
    eqG-cong : ∀ {A A' B B'} → Fib (eqG A A') → Fib (eqG B B') → Fib (eqG (eqG A B) (eqG A' B'))
    EqFib : ∀ {A B} → Fib A → Fib (eqG A B) → Fib B → Set k

  twoGraph : TwoGraph i j k
  twoGraph = record {
    graph = record {
      Vertex = Dom ;
      Path = λ A B → Fib (eqG A B);
      ref = ref} ;
    isTwoGraph = record {
      Fill = λ square → EqFib (RefGraph.Square.north square) (eqG-cong (RefGraph.Square.west square) (RefGraph.Square.east square)) (RefGraph.Square.south square) } }

  --TODO Inline?
  Eq : Dom → Dom → Set j
  Eq = TwoGraph.Path twoGraph

  Square : Set (i ⊔ j)
  Square = TwoGraph.Square twoGraph

  HasCong₂ : Set (i ⊔ j ⊔ k)
  HasCong₂ = ∀ {top bottom : Square} →
        TwoGraph.Fill twoGraph top → TwoGraph.Fill twoGraph bottom →
        EqFib (eqG-cong (TwoGraph.Square.north {r = twoGraph} top) (TwoGraph.Square.north {r = twoGraph} bottom))
          (eqG-cong (eqG-cong (TwoGraph.Square.west {r = twoGraph} top) (TwoGraph.Square.west {r = twoGraph} bottom))
            (eqG-cong (TwoGraph.Square.east {r = twoGraph} top) (TwoGraph.Square.east {r = twoGraph} bottom)))
          (eqG-cong (TwoGraph.Square.south {r = twoGraph} top) (TwoGraph.Square.south {r = twoGraph} bottom))

data RefGraphFunctor {i i' j j'} (S : RefGraph i j) (T : RefGraph i' j') : Set (i ⊔ i' ⊔ j ⊔ j') where
  mkRefGraphFunctor : ∀
    (point : RefGraph.Vertex S → RefGraph.Vertex T)
    (pathF : ∀ {x y} → RefGraph.Path S x y → RefGraph.Path T (point x) (point y)) →
    RefGraphFunctor S T

square : ∀ {i i' j j'} {S : RefGraph i j} {T : RefGraph i' j'} → RefGraphFunctor S T → RefGraph.Square S → RefGraph.Square T
square (mkRefGraphFunctor point pathF) sq = record
                { nw = point (RefGraph.Square.nw sq)
                ; ne = point (RefGraph.Square.ne sq)
                ; sw = point (RefGraph.Square.sw sq)
                ; se = point (RefGraph.Square.se sq)
                ; north = pathF (RefGraph.Square.north sq)
                ; south = pathF (RefGraph.Square.south sq)
                ; west = pathF (RefGraph.Square.west sq)
                ; east = pathF (RefGraph.Square.east sq)
                }

data TwoGraphFunctor {i i' j j' k k'} (S : TwoGraph i j k) (T : TwoGraph i' j' k') : Set (i ⊔ i' ⊔ j ⊔ j' ⊔ k ⊔ k') where
  mkTwoGraphFunctor : ∀ (graphFunctor : RefGraphFunctor (TwoGraph.graph S) (TwoGraph.graph T)) →
    (∀ {sq} → TwoGraph.Fill S sq → TwoGraph.Fill T (square graphFunctor sq)) →
    TwoGraphFunctor S T

app : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'} →
  TwoGraphFunctor S T → TwoGraph.Vertex S → TwoGraph.Vertex T
app (mkTwoGraphFunctor (mkRefGraphFunctor point _) _) = point

app₂ : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
  (F : TwoGraphFunctor S T) {x y} → TwoGraph.Path S x y → TwoGraph.Path T (app F x) (app F y)
app₂ (mkTwoGraphFunctor (mkRefGraphFunctor _ path) _) = path

postulate app₂-ref : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
                   (F : TwoGraphFunctor S T) (x : TwoGraph.Vertex S) →
                   app₂ F (TwoGraph.ref S x) ▷ TwoGraph.ref T (app F x)
{-# REWRITE app₂-ref #-}

gf : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'} →
  TwoGraphFunctor S T → RefGraphFunctor (TwoGraph.graph S) (TwoGraph.graph T)
gf F = mkRefGraphFunctor (app F) (app₂ F)

app₃ : ∀ {i i' j j' k k'} {S : TwoGraph i j k} {T : TwoGraph i' j' k'}
  (F : TwoGraphFunctor S T) {sq} → TwoGraph.Fill S sq → TwoGraph.Fill T (square (gf F) sq)
app₃ (mkTwoGraphFunctor (mkRefGraphFunctor _ _) isTwoGraphFunctor) = isTwoGraphFunctor


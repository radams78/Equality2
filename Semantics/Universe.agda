module Semantics.Universe where
open import Level
open import Semantics.RefGraph
open import Semantics.TwoGraph

-- A universe consists of:
-- * a set of (names of) types
-- * for any type A, a set of elements of A
-- * for any types A B, a type A = B
-- * for any a : A, p : A = B and b : B, a set a ~< p > b of paths from a to b over p
-- * for any A, an element ref A : A = A
-- * for any p : A = A' and q : B = B', an element p =* q : (A = B) = (A' = B')
record Universe i j k : Set (suc (i ⊔ j ⊔ k)) where
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
      Fill = λ square → EqFib (RefGraph.Square.north square)
        (eqG-cong (RefGraph.Square.west square) (RefGraph.Square.east square))
        (RefGraph.Square.south square) } }

  open TwoGraph twoGraph public renaming (Path to Eq)
  
  HasCong₂ : Set (i ⊔ j ⊔ k)
  HasCong₂ = ∀ {top bottom : Square} →
        TwoGraph.Fill twoGraph top → TwoGraph.Fill twoGraph bottom →
        EqFib (eqG-cong (Square.north top) (Square.north bottom))
          (eqG-cong (eqG-cong (Square.west top) (Square.west bottom))
            (eqG-cong (Square.east top) (Square.east bottom)))
          (eqG-cong (Square.south top) (Square.south bottom))

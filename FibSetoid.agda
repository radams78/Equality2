{-# OPTIONS --rewriting #-}
module FibSetoid where
open import Level

postulate _▷_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}

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
  
  record IsOneType k : Set (i ⊔ j ⊔ suc k) where
    field
      Fill : Square → Set k

record OneType i j k : Set (suc (i ⊔ j ⊔ k)) where
  field
    graph : RefGraph i j
    isOneType : RefGraph.IsOneType graph k

  open RefGraph graph public
  open IsOneType isOneType public

record FibSetoid i j k : Set (suc (i ⊔ j ⊔ k)) where
  field
    Dom  : Set i
    Fib  : Dom → Set j
    eqG  : Dom → Dom → Dom
    ref  : ∀ A → Fib (eqG A A)
    eqG-cong : ∀ {A A' B B'} → Fib (eqG A A') → Fib (eqG B B') → Fib (eqG (eqG A B) (eqG A' B'))
    EqFib : ∀ {A B} → Fib A → Fib (eqG A B) → Fib B → Set k

  oneType : OneType i j k
  oneType = record {
    graph = record {
      Vertex = Dom ;
      Path = λ A B → Fib (eqG A B);
      ref = ref} ;
    isOneType = record {
      Fill = λ square → EqFib (RefGraph.Square.north square) (eqG-cong (RefGraph.Square.west square) (RefGraph.Square.east square)) (RefGraph.Square.south square) } }

  --TODO Inline?
  Eq : Dom → Dom → Set j
  Eq = OneType.Path oneType

  Square : Set (i ⊔ j)
  Square = OneType.Square oneType

  HasCong₂ : Set (i ⊔ j ⊔ k)
  HasCong₂ = ∀ {top bottom : Square} →
        OneType.Fill oneType top → OneType.Fill oneType bottom →
        EqFib (eqG-cong (OneType.Square.north oneType top) (OneType.Square.north oneType bottom))
          (eqG-cong (eqG-cong (OneType.Square.west oneType top) (OneType.Square.west oneType bottom))
            (eqG-cong (OneType.Square.east oneType top) (OneType.Square.east oneType bottom)))
          (eqG-cong (OneType.Square.south oneType top) (OneType.Square.south oneType bottom))

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

data OneTypeFunctor {i i' j j' k k'} (S : OneType i j k) (T : OneType i' j' k') : Set (i ⊔ i' ⊔ j ⊔ j' ⊔ k ⊔ k') where
  mkOneTypeFunctor : ∀ (graphFunctor : RefGraphFunctor (OneType.graph S) (OneType.graph T)) →
    (∀ {sq} → OneType.Fill S sq → OneType.Fill T (square graphFunctor sq)) →
    OneTypeFunctor S T

app : ∀ {i i' j j' k k'} {S : OneType i j k} {T : OneType i' j' k'} →
  OneTypeFunctor S T → OneType.Vertex S → OneType.Vertex T
app (mkOneTypeFunctor (mkRefGraphFunctor point _) _) = point

app₂ : ∀ {i i' j j' k k'} {S : OneType i j k} {T : OneType i' j' k'}
  (F : OneTypeFunctor S T) {x y} → OneType.Path S x y → OneType.Path T (app F x) (app F y)
app₂ (mkOneTypeFunctor (mkRefGraphFunctor _ path) _) = path

postulate app₂-ref : ∀ {i i' j j' k k'} {S : OneType i j k} {T : OneType i' j' k'}
                   (F : OneTypeFunctor S T) (x : OneType.Vertex S) →
                   app₂ F (OneType.ref S x) ▷ OneType.ref T (app F x)
{-# REWRITE app₂-ref #-}

gf : ∀ {i i' j j' k k'} {S : OneType i j k} {T : OneType i' j' k'} →
  OneTypeFunctor S T → RefGraphFunctor (OneType.graph S) (OneType.graph T)
gf F = mkRefGraphFunctor (app F) (app₂ F)

app₃ : ∀ {i i' j j' k k'} {S : OneType i j k} {T : OneType i' j' k'}
  (F : OneTypeFunctor S T) {sq} → OneType.Fill S sq → OneType.Fill T (square (gf F) sq)
app₃ (mkOneTypeFunctor (mkRefGraphFunctor _ _) isOneTypeFunctor) = isOneTypeFunctor


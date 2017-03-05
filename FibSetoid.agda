module FibSetoid where
open import Level

record Graph i j : Set (suc (i ⊔ j)) where
  field
    Vertex  : Set i
    Path    : Vertex → Vertex → Set j

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
    graph : Graph i j
    isOneType : Graph.IsOneType graph k

  open Graph graph public
  open IsOneType isOneType public

record FibSetoid i j k : Set (suc (i ⊔ j ⊔ k)) where
  field
    Dom  : Set i
    Fib  : Dom → Set j
    eqG  : Dom → Dom → Dom
    eqG-cong : ∀ {A A' B B'} → Fib (eqG A A') → Fib (eqG B B') → Fib (eqG (eqG A B) (eqG A' B'))
    EqFib : ∀ {A B} → Fib A → Fib (eqG A B) → Fib B → Set k

  FS2OneType : OneType i j k
  FS2OneType = record {
    graph = record {
      Vertex = Dom ;
      Path = λ A B → Fib (eqG A B) } ;
    isOneType = record {
      Fill = λ square → EqFib (Graph.Square.north square) (eqG-cong (Graph.Square.west square) (Graph.Square.east square)) (Graph.Square.south square) } }

  --TODO Inline?
  Eq : Dom → Dom → Set j
  Eq = OneType.Path FS2OneType

  Square : Set (i ⊔ j)
  Square = OneType.Square FS2OneType

  HasCong₂ : Set (i ⊔ j ⊔ k)
  HasCong₂ = ∀ {top bottom : Square} →
        OneType.Fill FS2OneType top → OneType.Fill FS2OneType bottom →
        EqFib (eqG-cong (OneType.Square.north FS2OneType top) (OneType.Square.north FS2OneType bottom))
          (eqG-cong (eqG-cong (OneType.Square.west FS2OneType top) (OneType.Square.west FS2OneType bottom))
            (eqG-cong (OneType.Square.east FS2OneType top) (OneType.Square.east FS2OneType bottom)))
          (eqG-cong (OneType.Square.south FS2OneType top) (OneType.Square.south FS2OneType bottom))

module FibSetoid where

record FibSetoid : Set₁ where
  field
    Dom  : Set
    Fib  : Dom → Set
    eqG  : Dom → Dom → Dom
    eqG-cong : ∀ {A A' B B'} → Fib (eqG A A') → Fib (eqG B B') → Fib (eqG (eqG A B) (eqG A' B'))
    EqFib : ∀ {A B} → Fib A → Fib (eqG A B) → Fib B → Set

  Eq : Dom → Dom → Set
  Eq A B = Fib (eqG A B)

  record Square : Set where
    field
      nw : Dom
      ne : Dom
      sw : Dom
      se : Dom
      north : Eq nw ne
      south : Eq sw se
      west  : Eq nw sw
      east  : Eq ne se

    Fill : Set
    Fill = EqFib north (eqG-cong west east) south

  HasCong₂ : Set
  HasCong₂ = ∀ {top bottom : Square} →
        Square.Fill top → Square.Fill bottom →
        EqFib (eqG-cong (Square.north top) (Square.north bottom))
          (eqG-cong (eqG-cong (Square.west top) (Square.west bottom))
            (eqG-cong (Square.east top) (Square.east bottom)))
          (eqG-cong (Square.south top) (Square.south bottom))

module Univ.Sets where
open import Univ.Univ
open import Univ.Prp

-- Sets

postulate iso : Sets → Sets → Sets
_≃_ : Sets → Sets → Set
A ≃ B = El (iso A B)

postulate iso-cong : ∀ {A A' B B'} → A ≃ A' → B ≃ B' → iso A B ≃ iso A' B'

postulate eq : ∀ {A B} → El A → A ≃ B → El B → Prp
_∼⟪_⟫₀_ : ∀ {A B} → El A → A ≃ B → El B → Set
a ∼⟪ e ⟫₀ b = Prf (eq a e b)

record Square : Set where
  field
    nw : Sets
    ne : Sets
    sw : Sets
    se : Sets
    north : nw ≃ ne
    south : sw ≃ se
    west  : nw ≃ sw
    east  : ne ≃ se

  Fill : Set
  Fill = north ∼⟪ iso-cong west east ⟫₀ south

--TODO Refactor
postulate iso-cong₂' : ∀ {top bottom : Square} →
                     Square.Fill top →
                     Square.Fill bottom →
                     iso-cong (Square.north top) (Square.north bottom) ∼⟪ iso-cong (iso-cong (Square.west top) (Square.west bottom)) (iso-cong (Square.east top) (Square.east bottom)) ⟫₀ iso-cong (Square.south top) (Square.south bottom)
                     
postulate eq-cong : ∀ {A A' B B' a a' f f' b b'} {A* : A ≃ A'} {B* : B ≃ B'} → 
                  a ∼⟪ A* ⟫₀ a' → f ∼⟪ iso-cong A* B* ⟫₀ f' → b ∼⟪ B* ⟫₀ b' → 
                  eq a f b ↔ eq a' f' b'

postulate Ref₀ : ∀ A → A ≃ A

postulate Ref₀-cong : ∀ {A} {B} (e : A ≃ B) → Ref₀ A ∼⟪ iso-cong e e ⟫₀ Ref₀ B

postulate ref₀ : ∀ {A} {a} → a ∼⟪ Ref₀ A ⟫₀ a

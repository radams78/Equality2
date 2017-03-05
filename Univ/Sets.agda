module Univ.Sets where
open import FibSetoid
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

SETS : FibSetoid
SETS = record { Dom = Sets ; Fib = El ; eqG = iso ; eqG-cong = iso-cong ; EqFib = _∼⟪_⟫₀_ }

postulate eq-cong : ∀
                  {A A' B B' : Sets}
                  {e : A ≃ B} {e' : A' ≃ B'} {A* : A ≃ A'} {B* : B ≃ B'}
                  {a : El A} {a' : El A'} {b : El B} {b' : El B'} →
                  a ∼⟪ A* ⟫₀ a' → e ∼⟪ iso-cong A* B* ⟫₀ e' → b ∼⟪ B* ⟫₀ b' →
                  eq a e b ↔ eq a' e' b'
                  
postulate iso-cong₂' : FibSetoid.HasCong₂ SETS

postulate Ref₀ : ∀ A → A ≃ A

postulate Ref₀-cong : ∀ {A} {B} (e : A ≃ B) → Ref₀ A ∼⟪ iso-cong e e ⟫₀ Ref₀ B

postulate ref₀ : ∀ {A} {a} → a ∼⟪ Ref₀ A ⟫₀ a

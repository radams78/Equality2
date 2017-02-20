module Groupoid where

open import Function using (_∘_)
open import Data.Unit
open import Data.Product

data U : Set
El : U → Set

data U where

El ()

data Cx : Set
⟦_⟧C : Cx → Set

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : (Γ : Cx) → (⟦ Γ ⟧C → U) → Cx

⟦ ε ⟧C = ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] El (S γ)

infix 5 _∋_
data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧C → U) → Set where
  top : ∀ {Γ T} → Γ ,, T ∋ T ∘ proj₁
  pop : ∀ {Γ S T} → Γ ∋ T → Γ ,, S ∋ T ∘ proj₁

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → El (T γ)
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

data _⊢_ (Γ : Cx) : (⟦ Γ ⟧C → U) → Set
⟦_⟧⊢ : ∀ {Γ T} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → El (T γ)

data _⊢_ Γ where

  var : ∀ {T} → Γ ∋ T →
              ---------
                Γ ⊢ T

⟦ var x ⟧⊢ = ⟦ x ⟧∋
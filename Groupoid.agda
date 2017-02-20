module Groupoid where

open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Univ
open import Context U El

data tj (Γ : Cx) : (⟦ Γ ⟧C → U) → Set₁
syntax tj Γ (λ γ → A) = γ ∶ Γ ⊢ A
⟦_⟧⊢ : ∀ {Γ T} → tj Γ T → (γ : ⟦ Γ ⟧C) → El (T γ)

data tj Γ where

  var : ∀ {T} → 
      Γ ∋ T →
    ------------
    γ ∶ Γ ⊢ T γ

  One :
    ------------
    _ ∶ Γ ⊢ prop

⟦ var x ⟧⊢ = ⟦ x ⟧∋
⟦ One ⟧⊢ _ = ⊤
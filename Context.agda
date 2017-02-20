module Context (U : Set) (El : U → Set₁) where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product

data Cx : Set₁
⟦_⟧C : Cx → Set₁

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : (Γ : Cx) → (⟦ Γ ⟧C → U) → Cx

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] El (S γ)

infix 5 _∋_
data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧C → U) → Set₁ where
  top : ∀ {Γ T} → Γ ,, T ∋ T ∘ proj₁
  pop : ∀ {Γ S T} → Γ ∋ T → Γ ,, S ∋ T ∘ proj₁

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → El (T γ)
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ


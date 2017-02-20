module Context (U : Set) (El : U → Set) (EQU : U → U → Set) (EqEl : ∀ {A B} → El A → EQU A B → El B → Set) where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product

data Cx : Set₁
⟦_⟧C : Cx → Set₁
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set

infix 75 _,,_,,_
data Cx where
  ε : Cx
  _,,_,,_ : (Γ : Cx) (S : ⟦ Γ ⟧C → U) → (∀ γ γ' → EQC Γ γ γ' → EQU (S γ) (S γ')) → Cx

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ,, S* ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] El (S γ)

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S ,, S*) (γ , s) (γ' , s') = Σ[ p ∈ EQC Γ γ γ' ] EqEl s (S* γ γ' p) s'

infix 5 _∋_
data _∋_ : (Γ : Cx) (T : ⟦ Γ ⟧C → U) → Set₁ where
  top : ∀ {Γ T T*} → Γ ,, T ,, T* ∋ T ∘ proj₁
  pop : ∀ {Γ S S* T} → Γ ∋ T → Γ ,, S ,, S* ∋ T ∘ proj₁

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → El (T γ)
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ


module Groupoid where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Univ
open import Context

K : U → ∀ Γ → Type Γ
K A _ = record { 
  obj = λ _ → A ; 
  obj-cong = λ _ → Ref A ;
  obj-cong₂ = λ _ → Ref-cong (Ref A) }

data _⊢_ (Γ : Cx) : Type Γ → Set₁
⟦_⟧⊢ : ∀ {Γ T} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦_⟧⊢-cong : ∀ {Γ T} (t : Γ ⊢ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ t ⟧⊢ γ ∼〈 γ* 〉 ⟦ t ⟧⊢ γ'
⟦_⟧⊢-cong₂ : ∀ {Γ T} (t : Γ ⊢ T) {a₁ a₂ b₁ b₂}
  {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  ⟦ t ⟧⊢-cong a* ∼〈〈 path-cong (⟦ t ⟧⊢-cong p₁) (Type.obj-cong₂ T sq) (⟦ t ⟧⊢-cong p₂) 〉〉₀ ⟦ t ⟧⊢-cong b*

data _⊢_ Γ where

  VAR : ∀ {T} → 
      Γ ∋ T →
    ------------
      Γ ⊢ T

  PRP :
    ----------------
      Γ ⊢ K sets Γ

⟦ VAR x ⟧⊢ = ⟦ x ⟧∋
⟦ PRP ⟧⊢ _ = prp

⟦ VAR x ⟧⊢-cong γ* = ⟦ x ⟧∋-cong γ*
⟦ PRP ⟧⊢-cong γ* = ref prp

⟦ VAR x ⟧⊢-cong₂ γ₂ = ⟦ x ⟧∋-cong₂ γ₂
⟦ PRP ⟧⊢-cong₂ γ₂ = ref-cong (ref prp)

data _⊢₀_ (Γ : Cx) : Setover Γ → Set₁ where

⟦_⟧⊢₀ : ∀ {Γ T} → Γ ⊢₀ T → (γ : ⟦ Γ ⟧C) → El (Setover.obj T γ)
⟦ () ⟧⊢₀

⟦_⟧⊢₀-cong : ∀ {Γ T} (t : Γ ⊢₀ T) {γ γ'} (γ* : EQC Γ γ γ') → ⟦ t ⟧⊢₀ γ ∼〈〈 Setover.obj-cong T γ* 〉〉₀ ⟦ t ⟧⊢₀ γ'
⟦ () ⟧⊢₀-cong

--A substitution or context morphism from Γ to Δ
data Sub (Γ : Cx) : Cx → Set₁
⟦_⟧s : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧s-cong : ∀ {Γ Δ} (σ : Sub Γ Δ) {γ γ' : ⟦ Γ ⟧C} → EQC Γ γ γ' → EQC Δ (⟦ σ ⟧s γ) (⟦ σ ⟧s γ')
⟦_⟧s-cong₂ : ∀ {Γ Δ} (σ : Sub Γ Δ) {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} 
  {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂} →
  EQC₂ {Γ} a* b* p₁ p₂ → EQC₂ {Δ} (⟦ σ ⟧s-cong a*) (⟦ σ ⟧s-cong b*) (⟦ σ ⟧s-cong p₁) (⟦ σ ⟧s-cong p₂)
TypeF : ∀ {Γ Δ} → Sub Γ Δ → Type Δ → Type Γ

data Sub Γ where
  • : Sub Γ ε
  _,,,_ : ∀ {Δ T} (σ : Sub Γ Δ) → Γ ⊢ TypeF σ T → Sub Γ (Δ ,, T)

TypeF σ T = record { 
  obj = λ γ → Type.obj T (⟦ σ ⟧s γ) ; 
  obj-cong = λ γ* → Type.obj-cong T (⟦ σ ⟧s-cong γ*) ;
  obj-cong₂ = λ γ₂ → Type.obj-cong₂ T (⟦ σ ⟧s-cong₂ γ₂) }

⟦ • ⟧s γ = lift ⊤.tt
⟦ σ ,,, t ⟧s γ = ⟦ σ ⟧s γ , ⟦ t ⟧⊢ γ

⟦ • ⟧s-cong _ = ⊤.tt
⟦ σ ,,, t ⟧s-cong γ* = (⟦ σ ⟧s-cong γ*) , ⟦ t ⟧⊢-cong γ*

⟦ • ⟧s-cong₂ _ = ⊤.tt
⟦ σ ,,, t ⟧s-cong₂ γ₂ = (⟦ σ ⟧s-cong₂ γ₂) , ⟦ t ⟧⊢-cong₂ γ₂

ap : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ∋ T → Γ ⊢ TypeF σ T
ap (_ ,,, t) top = t
ap (σ ,,, _) (pop x) = ap σ x

ap-sound : ∀ {Γ Δ T} {σ : Sub Γ Δ} {x : Δ ∋ T} {γ} → ⟦ ap σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (⟦ σ ⟧s γ)
ap-sound {σ = •} {x = ()}
ap-sound {σ = _ ,,, _} {x = top} = refl
ap-sound {σ = _ ,,, _} {pop x} = ap-sound {x = x}

sub : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ⊢ T → Γ ⊢ TypeF σ T
sub σ (VAR x) = ap σ x
sub σ PRP = PRP

sub-sound : ∀ {Γ Δ T} {σ : Sub Γ Δ} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (⟦ σ ⟧s γ)
sub-sound {t = VAR x} = ap-sound {x = x}
sub-sound {t = PRP} = refl

data PathSub : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
⟦_⟧ps : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)
⟦_⟧ps-cong : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) {γ γ'} (γ* : EQC Γ γ γ') →
  EQC₂ {Δ} (⟦ τ ⟧ps γ) (⟦ τ ⟧ps γ') (⟦ ρ ⟧s-cong γ*) (⟦ σ ⟧s-cong γ*)

data PathSub where
  • : ∀ {Γ} → PathSub {Γ} • •
  _,,,_ : ∀ {Γ Δ T} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → Γ ⊢₀ record { 
    obj = λ γ → path (⟦ s ⟧⊢ γ) (Type.obj-cong T (⟦ τ ⟧ps γ)) (⟦ t ⟧⊢ γ) ;
    obj-cong = λ {γ} {γ'} γ* → path-cong (⟦ s ⟧⊢-cong γ*) (Type.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (⟦ t ⟧⊢-cong γ*) } →
       PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t)

⟦ • ⟧ps γ = ⊤.tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , ⟦ b* ⟧⊢₀ γ

⟦ • ⟧ps-cong γ* = ⊤.tt
⟦ τ ,,, b* ⟧ps-cong γ* = (⟦ τ ⟧ps-cong γ*) , (⟦ b* ⟧⊢₀-cong γ*)
module Syntax where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Univ
open import Context

data _⊢_ (Γ : Cx) : ∀ {n} → Typeover n Γ → Set₁
⟦_⟧⊢ : ∀ {Γ n} {T : Typeover n Γ} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦_⟧⊢-cong : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ t ⟧⊢ γ ∼〈 γ* 〉 ⟦ t ⟧⊢ γ'
⟦_⟧⊢-cong₂ : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {a₁ a₂ b₁ b₂}
  {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ pred n ] ⟦ t ⟧⊢-cong a* ∼⟪ eqTTn-cong {n} (⟦ t ⟧⊢-cong p₁) (Typeover.obj-cong₂ T sq) (⟦ t ⟧⊢-cong p₂) ⟫ ⟦ t ⟧⊢-cong b*

data _⊢_ Γ where

  VAR : ∀ {n} {T : Typeover n Γ} → 
      Γ ∋ T →
    ------------
      Γ ⊢ T

  PRP :
    --------------------
      Γ ⊢ K hone Γ sets

⟦ VAR x ⟧⊢ = ⟦ x ⟧∋
⟦ PRP ⟧⊢ _ = prp

⟦ VAR x ⟧⊢-cong γ* = ⟦ x ⟧∋-cong γ*
⟦ PRP ⟧⊢-cong γ* = ref prp

⟦ VAR x ⟧⊢-cong₂ γ₂ = ⟦ x ⟧∋-cong₂ γ₂
⟦ PRP ⟧⊢-cong₂ γ₂ = ref-cong (ref prp)

--A substitution or context morphism from Γ to Δ
data Sub (Γ : Cx) : Cx → Set₁
⟦_⟧s : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧s-cong : ∀ {Γ Δ} (σ : Sub Γ Δ) {γ γ' : ⟦ Γ ⟧C} → EQC Γ γ γ' → EQC Δ (⟦ σ ⟧s γ) (⟦ σ ⟧s γ')
⟦_⟧s-cong₂ : ∀ {Γ Δ} (σ : Sub Γ Δ) {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} 
  {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂} →
  EQC₂ {Γ} a* b* p₁ p₂ → EQC₂ {Δ} (⟦ σ ⟧s-cong a*) (⟦ σ ⟧s-cong b*) (⟦ σ ⟧s-cong p₁) (⟦ σ ⟧s-cong p₂)
TypeoverF : ∀ {n Γ Δ} → Sub Γ Δ → Typeover n Δ → Typeover n Γ

data Sub Γ where
  • : Sub Γ ε
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} (σ : Sub Γ Δ) → Γ ⊢ TypeoverF σ T → Sub Γ (Δ ,, T)

TypeoverF σ T = record { 
  obj = λ γ → Typeover.obj T (⟦ σ ⟧s γ) ; 
  obj-cong = λ γ* → Typeover.obj-cong T (⟦ σ ⟧s-cong γ*) ;
  obj-cong₂ = λ γ₂ → Typeover.obj-cong₂ T (⟦ σ ⟧s-cong₂ γ₂) ;
  obj-cong₃ = λ γsq δsq sq₁ sq₂ sqₑ sqₑ' → Typeover.obj-cong₃ T (⟦ σ ⟧s-cong₂ γsq) (⟦ σ ⟧s-cong₂ δsq) (⟦ σ ⟧s-cong₂ sq₁) (⟦ σ ⟧s-cong₂ sq₂) (⟦ σ ⟧s-cong₂ sqₑ) (⟦ σ ⟧s-cong₂ sqₑ')}

⟦ • ⟧s γ = lift ⊤.tt
⟦ σ ,,, t ⟧s γ = ⟦ σ ⟧s γ , ⟦ t ⟧⊢ γ

⟦ • ⟧s-cong _ = ⊤.tt
⟦ σ ,,, t ⟧s-cong γ* = (⟦ σ ⟧s-cong γ*) , ⟦ t ⟧⊢-cong γ*

⟦ • ⟧s-cong₂ _ = ⊤.tt
⟦ σ ,,, t ⟧s-cong₂ γ₂ = (⟦ σ ⟧s-cong₂ γ₂) , ⟦ t ⟧⊢-cong₂ γ₂

ap : ∀ {Γ Δ n} {T : Typeover n Δ} (σ : Sub Γ Δ) → Δ ∋ T → Γ ⊢ TypeoverF σ T
ap (_ ,,, t) top = t
ap (σ ,,, _) (pop x) = ap σ x

ap-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {x : Δ ∋ T} {γ} → ⟦ ap σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (⟦ σ ⟧s γ)
ap-sound {σ = _ ,,, _} {x = top} = refl
ap-sound {σ = _ ,,, _} {pop x} = ap-sound {x = x}

sub : ∀ {n Γ Δ} {T : Typeover n Δ} (σ : Sub Γ Δ) → Δ ⊢ T → Γ ⊢ TypeoverF σ T
sub σ (VAR x) = ap σ x
sub σ PRP = PRP

sub-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (⟦ σ ⟧s γ)
sub-sound {t = VAR x} = ap-sound {x = x}
sub-sound {t = PRP} = refl

data PathSub : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
⟦_⟧ps : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)
⟦_⟧ps-cong : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) {γ γ'} (γ* : EQC Γ γ γ') →
  EQC₂ {Δ} (⟦ τ ⟧ps γ) (⟦ τ ⟧ps γ') (⟦ ρ ⟧s-cong γ*) (⟦ σ ⟧s-cong γ*)

data PathSub where
  • : ∀ {Γ} → PathSub {Γ} • •
  _,,,_ : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → Γ ⊢ record { 
    obj = λ γ → eqTTn {n} (⟦ s ⟧⊢ γ) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (⟦ t ⟧⊢ γ) ;
    obj-cong = λ {γ} {γ'} γ* → eqTTn-cong {n} (⟦ s ⟧⊢-cong γ*) (Typeover.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (⟦ t ⟧⊢-cong γ*) ;
    obj-cong₂ = λ γ* → {!eqTTn-cong₂!} ;
    obj-cong₃ = {!!}} →
       PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t)

⟦ • ⟧ps γ = ⊤.tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , ⟦ b* ⟧⊢ γ

⟦ • ⟧ps-cong γ* = ⊤.tt
⟦ τ ,,, b* ⟧ps-cong γ* = (⟦ τ ⟧ps-cong γ*) , (⟦ b* ⟧⊢-cong γ*)

apps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) →
  Γ ⊢ record {
    obj = λ γ → eqTTn {!!} {!!} {!!} ; obj-cong = {!!} ; obj-cong₂ = {!!} ; obj-cong₃ = {!!} }
apps τ x = {!!}

{-# OPTIONS --rewriting #-}
module Syntax where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Univ
open import Univ.HLevel
open import Context

--TODO Remove old equality constructions in Univ
--TODO Extract function for ap₂ ∘ Typeover.obj-cong T

--TODO Common pattern with Functor
data Functor' (Γ Δ : Cx) (F : ⟦ Γ ⟧C → ⟦ Δ ⟧C) : Set₁ where
  make-Functor' : (∀ {γ γ'} → EQC Γ γ γ' → EQC Δ (F γ) (F γ')) → Functor' Γ Δ F

ap₂' : ∀ {Γ Δ F γ γ'} → Functor' Γ Δ F → EQC Γ γ γ' → EQC Δ (F γ) (F γ')
ap₂' (make-Functor' F-cong) γ* = F-cong γ*

postulate ap₂'-ref : ∀ {Γ Δ F γ} (F-cong : Functor' Γ Δ F) → ap₂' F-cong (RefC γ) ▷ RefC (F γ)
{-# REWRITE ap₂'-ref #-}

data Functor₂' {Γ Δ : Cx} {F : ⟦ Γ ⟧C → ⟦ Δ ⟧C} (F-cong : Functor' Γ Δ F) : Set₁ where
  make-Functor₂' : (∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} →
    EQC₂ {Γ} γ₁* γ₂* γₑ γₑ' → EQC₂ {Δ} (ap₂' F-cong γ₁*) (ap₂' F-cong γ₂*) (ap₂' F-cong γₑ) (ap₂' F-cong γₑ')) →
    Functor₂' F-cong

ap₃' : ∀ {Γ Δ F F-cong γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} →
  Functor₂' {Γ} {Δ} {F} F-cong → EQC₂ {Γ} γ₁* γ₂* γₑ γₑ' → EQC₂ {Δ} (ap₂' F-cong γ₁*) (ap₂' F-cong γ₂*) (ap₂' F-cong γₑ) (ap₂' F-cong γₑ')
ap₃' (make-Functor₂' F-cong₂) = F-cong₂

postulate ap₃'-ref : ∀ {Γ Δ F F-cong γ γ'} (F-cong₂ : Functor₂' {Γ} {Δ} {F} F-cong) (γ* : EQC Γ γ γ') →
                   ap₃' F-cong₂ (RefC-cong γ*) ▷ RefC-cong (ap₂' F-cong γ*)
{-# REWRITE ap₃'-ref #-}

data _⊢_ (Γ : Cx) : ∀ {n} → Typeover n Γ → Set₁
⟦_⟧⊢ : ∀ {Γ n} {T : Typeover n Γ} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦_⟧⊢-cong : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ t ⟧⊢ γ ∼〈 γ* 〉 ⟦ t ⟧⊢ γ'
⟦_⟧⊢-cong₂ : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {a₁ a₂ b₁ b₂}
  {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ pred n ] ⟦ t ⟧⊢-cong a* ∼⟪ eqTTn-cong n (⟦ t ⟧⊢-cong p₁) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) (⟦ t ⟧⊢-cong p₂) ⟫ ⟦ t ⟧⊢-cong b*

data _⊢_ Γ where

  VAR : ∀ {n} {T : Typeover n Γ} → 
      Γ ∋ T →
    ------------
      Γ ⊢ T

  PRP :
    --------------------
      Γ ⊢ K hone Γ sets

--TODO Extract the type below
  REF : ∀ {n} {T : Typeover n Γ} →
      (t : Γ ⊢ T) →
    -----------------
      Γ ⊢ record { obj = λ γ → eqTTn (⟦ t ⟧⊢ γ) (ap₂ (Typeover.obj-cong T) (RefC γ)) (⟦ t ⟧⊢ γ) ;
                   obj-cong = make-Functor (λ γ* → eqTTn-cong n (⟦ t ⟧⊢-cong γ*) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ (RefC-cong γ*)) (⟦ t ⟧⊢-cong γ*)) ;
                   obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (⟦ t ⟧⊢-cong₂ sq-fill) (Typeover.obj-cong₃ T (RefC-cong γ₁*) (RefC-cong γ₂*) (RefC-cong γₑ) (RefC-cong γₑ') sq-fill sq-fill) (⟦ t ⟧⊢-cong₂ sq-fill)) ;
                   obj-cong₃ = λ _ _ _ _ _ _ → trivial n }

--TODO Make n explicit in refn, refn-cong
⟦ VAR x ⟧⊢ = ⟦ x ⟧∋
⟦ PRP ⟧⊢ _ = prp
⟦ REF {n} t ⟧⊢ γ = refn {n} (⟦ t ⟧⊢ γ)

⟦ VAR x ⟧⊢-cong γ* = ⟦ x ⟧∋-cong γ*
⟦ PRP ⟧⊢-cong γ* = ref prp
⟦ REF {n} t ⟧⊢-cong γ* = refn-cong {n} (⟦ t ⟧⊢-cong γ*)

⟦ VAR x ⟧⊢-cong₂ γ₂ = ⟦ x ⟧∋-cong₂ γ₂
⟦ PRP ⟧⊢-cong₂ γ₂ = ref-cong (ref prp)
⟦ REF {n} _ ⟧⊢-cong₂ _ = trivial n

--A substitution or context morphism from Γ to Δ
data Sub (Γ : Cx) : Cx → Set₁
⟦_⟧s : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧s-cong : ∀ {Γ Δ} (σ : Sub Γ Δ) → Functor' Γ Δ ⟦ σ ⟧s
⟦_⟧s-cong₂ : ∀ {Γ Δ} (σ : Sub Γ Δ) → Functor₂' ⟦ σ ⟧s-cong
TypeoverF : ∀ {n Γ Δ} → Sub Γ Δ → Typeover n Δ → Typeover n Γ

data Sub Γ where
  • : Sub Γ ε
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} (σ : Sub Γ Δ) → Γ ⊢ TypeoverF σ T → Sub Γ (Δ ,, T)

TypeoverF σ T = record { 
  obj = λ γ → Typeover.obj T (⟦ σ ⟧s γ) ; 
  obj-cong = make-Functor (λ γ* → ap₂ (Typeover.obj-cong T) (ap₂' ⟦ σ ⟧s-cong γ*)) ;
  obj-cong₂ = make-Functor₂ λ _ _ _ _ γ₂ → ap₃ (Typeover.obj-cong₂ T) _ _ _ _  (ap₃' ⟦ σ ⟧s-cong₂ γ₂) ;
  obj-cong₃ = λ γsq δsq sq₁ sq₂ sqₑ sqₑ' → Typeover.obj-cong₃ T (ap₃' ⟦ σ ⟧s-cong₂ γsq) (ap₃' ⟦ σ ⟧s-cong₂ δsq) (ap₃' ⟦ σ ⟧s-cong₂ sq₁) (ap₃' ⟦ σ ⟧s-cong₂ sq₂) (ap₃' ⟦ σ ⟧s-cong₂ sqₑ) (ap₃' ⟦ σ ⟧s-cong₂ sqₑ')}

⟦ • ⟧s γ = lift ⊤.tt
⟦ σ ,,, t ⟧s γ = ⟦ σ ⟧s γ , ⟦ t ⟧⊢ γ

⟦ • ⟧s-cong = make-Functor' (λ _ → ⊤.tt)
⟦ σ ,,, t ⟧s-cong = make-Functor' (λ γ* → ap₂' ⟦ σ ⟧s-cong γ* , ⟦ t ⟧⊢-cong γ*)

⟦ • ⟧s-cong₂ = make-Functor₂' (λ _ → ⊤.tt)
⟦ σ ,,, t ⟧s-cong₂ = make-Functor₂' (λ γ₂ → (ap₃' ⟦ σ ⟧s-cong₂ γ₂) , ⟦ t ⟧⊢-cong₂ γ₂)

ap : ∀ {Γ Δ n} {T : Typeover n Δ} (σ : Sub Γ Δ) → Δ ∋ T → Γ ⊢ TypeoverF σ T
ap (_ ,,, t) top = t
ap (σ ,,, _) (pop x) = ap σ x

ap-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {x : Δ ∋ T} {γ} → ⟦ ap σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (⟦ σ ⟧s γ)
ap-sound {σ = _ ,,, _} {x = top} = refl
ap-sound {σ = _ ,,, _} {pop x} = ap-sound {x = x}

sub : ∀ {n Γ Δ} {T : Typeover n Δ} (σ : Sub Γ Δ) → Δ ⊢ T → Γ ⊢ TypeoverF σ T
sub σ (VAR x) = ap σ x
sub σ PRP = PRP
sub .{pred n} {Γ} {_} σ (REF {n} {T} t) = {!REF (sub σ t)!}

sub-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (⟦ σ ⟧s γ)
sub-sound {t = VAR x} = ap-sound {x = x}
sub-sound {t = PRP} = refl
sub-sound {t = REF t} = {!!}

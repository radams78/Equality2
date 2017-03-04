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
  make-Functor' : (∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC Δ (F γ) (F γ')) → Functor' Γ Δ F

ap₂' : ∀ {Γ Δ F γ γ'} → Functor' Γ Δ F → EQC Γ γ γ' → EQC Δ (F γ) (F γ')
ap₂' (make-Functor' F-cong) γ* = F-cong γ*

postulate ap₂'-ref : ∀ {Γ Δ F γ} (F-cong : Functor' Γ Δ F) → ap₂' F-cong (RefC γ) ▷ RefC (F γ)
{-# REWRITE ap₂'-ref #-}

data Functor₂' {Γ Δ : Cx} {F : ⟦ Γ ⟧C → ⟦ Δ ⟧C} (F-cong : Functor' Γ Δ F) : Set₁ where
  make-Functor₂' : (∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
    (sq-fill : EQC₂ {Γ} γ₁* γ₂* γₑ γₑ') → EQC₂ {Δ} (ap₂' F-cong γ₁*) (ap₂' F-cong γ₂*) (ap₂' F-cong γₑ) (ap₂' F-cong γₑ')) →
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

--TODO Extract notion of functor between Γ and Δ
TypeoverF : ∀ {n} {Γ Δ} (σs : (γ : ⟦ Γ ⟧C) → ⟦ Δ ⟧C)
  (σs-cong : Functor' Γ Δ σs) (σs-cong₂ : Functor₂' σs-cong) (T : Typeover n Δ) → Typeover n Γ
TypeoverF σs σs-cong σs-cong₂ T = record {
  obj = λ γ → Typeover.obj T (σs γ) ;
  obj-cong = make-Functor (λ γ* → ap₂ (Typeover.obj-cong T) (ap₂' σs-cong γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → ap₃ (Typeover.obj-cong₂ T) (ap₂' σs-cong γ₁*) (ap₂' σs-cong γ₂*) (ap₂' σs-cong γₑ) (ap₂' σs-cong γₑ') (ap₃' σs-cong₂ sq-fill)) ;
  obj-cong₃ = λ γsq δsq sq₁ sq₂ sqₑ sqₑ' → Typeover.obj-cong₃ T (ap₃' σs-cong₂ γsq) (ap₃' σs-cong₂ δsq) (ap₃' σs-cong₂ sq₁) (ap₃' σs-cong₂ sq₂) (ap₃' σs-cong₂ sqₑ) (ap₃' σs-cong₂ sqₑ') }

--A substitution or context morphism from Γ to Δ
data Sub Γ : ∀ (Δ : Cx)
  (map₁ : (γ : ⟦ Γ ⟧C) → ⟦ Δ ⟧C)
  (map₂ : Functor' Γ Δ map₁) →
  Functor₂' map₂ → Set₁
--TypeoverF : ∀ {n Γ Δ} → Sub Γ Δ → Typeover n Δ → Typeover n Γ

data Sub Γ where
  • : Sub Γ ε (λ _ → lift tt) (make-Functor' (λ _ → tt)) (make-Functor₂' (λ _ → tt)) 
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} {σs} {σs-cong} {σs-cong₂} (σ : Sub Γ Δ σs σs-cong σs-cong₂)
    (t : Γ ⊢ TypeoverF σs σs-cong σs-cong₂ T) →
    Sub Γ (Δ ,, T) (λ γ → σs γ , ⟦ t ⟧⊢ γ)
      (make-Functor' (λ γ* → ap₂' σs-cong γ* , ⟦ t ⟧⊢-cong γ*))
      (make-Functor₂' (λ sq-fill → ap₃' σs-cong₂ sq-fill , ⟦ t ⟧⊢-cong₂ sq-fill))

ap : ∀ {Γ Δ n} {T : Typeover n Δ} {σs} {σs-cong} {σs-cong₂} (σ : Sub Γ Δ σs σs-cong σs-cong₂) → Δ ∋ T → Γ ⊢ TypeoverF σs σs-cong σs-cong₂ T
ap (_ ,,, t) top = t
ap (σ ,,, _) (pop x) = ap σ x

ap-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σs} {σs-cong} {σs-cong₂} {σ : Sub Γ Δ σs σs-cong σs-cong₂} {x : Δ ∋ T} {γ} → ⟦ ap σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (σs γ)
ap-sound {σ = _ ,,, _} {x = top} = refl
ap-sound {σ = _ ,,, _} {pop x} = ap-sound {x = x}

sub : ∀ {n Γ Δ} {T : Typeover n Δ} {σs} {σs-cong} {σs-cong₂} (σ : Sub Γ Δ σs σs-cong σs-cong₂) → Δ ⊢ T → Γ ⊢ TypeoverF σs σs-cong σs-cong₂ T
sub σ (VAR x) = ap σ x
sub σ PRP = PRP
sub .{pred n} {Γ} {_} σ (REF {n} {T} t) = {!REF!}

sub-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σs} {σs-cong} {σs-cong₂} {σ : Sub Γ Δ σs σs-cong σs-cong₂} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (σs γ)
sub-sound {t = VAR x} = ap-sound {x = x}
sub-sound {t = PRP} = refl
sub-sound {t = REF t} = {!!}

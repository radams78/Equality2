{-# OPTIONS --rewriting #-}
module Syntax where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Univ
open import Context

open Context.Functors

module constant {n : hLevel} {Γ : Cx} (A : Type n) where
  postulate functorK : Functor (CONTEXT Γ) (TYPE n)
  postulate apK : ∀ γ → ap _ _ functorK γ ▷ A
  {-# REWRITE apK #-}
  postulate ap2K : ∀ {γ} {γ'} (γ* : EQC Γ γ γ') → ap2 _ _ functorK γ* ▷ Refn A
  {-# REWRITE ap2K #-}
open constant

postulate apSets : ∀ {Γ : Cx} (γ : ⟦ Γ ⟧C) → ap _ _ (functorK sets) γ ▷ sets
{-# REWRITE apSets #-}
postulate ap2Sets : ∀ {Γ γ γ'} (γ* : EQC Γ γ γ') → ap2 _ _ (functorK sets) γ* ▷ Refn sets
{-# REWRITE ap2Sets #-}
--Need this separately for some reason - bug?

K : ∀ n Γ → Type n → Typeover n Γ
K n _ A = record { 
  obj = functorK A ;
  obj-cong₂ = λ _ _ → Refn-cong (Refn A);
  obj-cong₃ = λ _ _ _ _ _ _ _ → Refn-cong₂ {n} (Refn-cong (Refn A))}

data _⊢_ (Γ : Cx) : ∀ {n} → Typeover n Γ → Set₁
⟦_⟧⊢ : ∀ {Γ n} {T : Typeover n Γ} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦_⟧⊢-cong : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ t ⟧⊢ γ ∼〈 γ* 〉 ⟦ t ⟧⊢ γ'
⟦_⟧⊢-square : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) (sq : Square Γ) → Squareover T sq
⟦_⟧⊢-cong₂ : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {sq : Square Γ} (sq-fill : EQC₂ {Γ} sq) → Squareover.Fill (⟦ t ⟧⊢-square sq) sq-fill

module EQ {n Γ} {T : Typeover n Γ} (t : Γ ⊢ T) where
  postulate EQ : Functor (CONTEXT Γ) (TYPE (pred n))
  postulate apEQ : ∀ (γ : ⟦ Γ ⟧C) → ap _ _ EQ γ ▷ eqTTn (⟦ t ⟧⊢ γ) (Refn (ap _ _ (Typeover.obj T) γ)) (⟦ t ⟧⊢ γ)
  {-# REWRITE apEQ #-}
  postulate ap2EQ : ∀ {γ γ'} (γ* : EQC Γ γ γ') → ap2 _ _ EQ γ* ▷ eqTTn-cong n (⟦ t ⟧⊢-cong γ*) (Refn-cong (ap2 _ _ (Typeover.obj T) γ*)) (⟦ t ⟧⊢-cong γ*)
  {-# REWRITE ap2EQ #-}

open EQ

⟦ t ⟧⊢-square = square-section ⟦ t ⟧⊢ ⟦ t ⟧⊢-cong

data _⊢_ Γ where

  VAR : ∀ {n} {T : Typeover n Γ} → 
      Γ ∋ T →
    ------------
      Γ ⊢ T

  PRP :
    --------------------
      Γ ⊢ K hone Γ sets

  REF : ∀ {n} {T : Typeover n Γ} →
    (t : Γ ⊢ T) →
  -----------------
    Γ ⊢ record { obj = EQ t ;
               obj-cong₂ = λ sq sq-fill → eqTTn-cong₂ {n} (⟦ t ⟧⊢-cong₂ sq-fill) (Refn-cong₂ {n} (Typeover.obj-cong₂ T sq sq-fill)) (⟦ t ⟧⊢-cong₂ sq-fill) ;
               obj-cong₃ = λ _ _ _ _ _ _ _ → trivial {n} _ _ _ }

⟦ VAR x ⟧⊢ = ⟦ x ⟧∋
⟦ PRP ⟧⊢ γ = prp
⟦ REF t ⟧⊢ γ = refn (⟦ t ⟧⊢ γ)

⟦ VAR x ⟧⊢-cong γ* = ⟦ x ⟧∋-cong γ*
⟦ PRP ⟧⊢-cong γ* = refn prp
⟦ REF {n} {T} t ⟧⊢-cong γ* = refn-cong n (ap2 _ _ (Typeover.obj T) γ*) (⟦ t ⟧⊢-cong γ*)

⟦ VAR x ⟧⊢-cong₂ γ₂ = ⟦ x ⟧∋-cong₂ _ γ₂
⟦ PRP ⟧⊢-cong₂ γ₂ = refn-cong hone (Ref sets) (refn prp)
⟦ REF {n} t ⟧⊢-cong₂ γ₂ = trivial {n} _ _ _
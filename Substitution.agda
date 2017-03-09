{-# OPTIONS --rewriting #-}
module Substitution where
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Context
open import Syntax

open Functors
open weakening
open weak-Functor

--A substitution or context morphism from Γ to Δ
data Sub (Γ : Cx) : Cx → Set₁
⟦_⟧s : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦_⟧s-cong : ∀ {Γ Δ} (σ : Sub Γ Δ) {γ γ' : ⟦ Γ ⟧C} → EQC Γ γ γ' → EQC Δ (⟦ σ ⟧s γ) (⟦ σ ⟧s γ')
⟦_⟧s-square : ∀ {Γ Δ} (σ : Sub Γ Δ) → Square Γ → Square Δ
⟦_⟧s-cong₂ : ∀ {Γ Δ} (σ : Sub Γ Δ) {sq : Square Γ} → EQC₂ {Γ} sq → EQC₂ {Δ} (⟦ σ ⟧s-square sq)
TypeoverF : ∀ {n Γ Δ} → Sub Γ Δ → Typeover n Δ → Typeover n Γ

data Sub Γ where
  • : Sub Γ ε
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} (σ : Sub Γ Δ) → Γ ⊢ TypeoverF σ T → Sub Γ (Δ ,, T)
--TODO Substitutions into sets and propositions

⟦ σ ⟧s-square = square-functor ⟦ σ ⟧s ⟦ σ ⟧s-cong

module subFunctor {n Γ Δ} (σ : Sub Γ Δ) (F : Functor (CONTEXT Δ) (TYPE n)) where
  postulate subFunctor : Functor (CONTEXT Γ) (TYPE n)
  postulate apsubFunctor : ∀ γ → ap _ _ subFunctor γ ▷ ap _ _ F (⟦ σ ⟧s γ)
  {-# REWRITE apsubFunctor #-}
  postulate ap2subFunctor : ∀ {γ γ'} (γ* : EQC Γ γ γ') → ap2 _ _ subFunctor γ* ▷ ap2 _ _ F (⟦ σ ⟧s-cong γ*)
  {-# REWRITE ap2subFunctor #-}

open subFunctor

postulate subFunctor-weakFunctor : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {t : Γ ⊢ TypeoverF σ T} (F : Functor (CONTEXT Δ) (TYPE n)) → subFunctor (σ ,,, t) (weak-Functor {T = T} F) ▷ subFunctor σ F
{-# REWRITE subFunctor-weakFunctor #-}

TypeoverF σ T = record { 
  obj = subFunctor σ (Typeover.obj T) ;
  obj-cong₂ = λ _ γ₂ → Typeover.obj-cong₂ T _ (⟦ σ ⟧s-cong₂ γ₂);
  obj-cong₃ = λ _ γsq δsq sq₁ sq₂ sqₑ sqₑ' → Typeover.obj-cong₃ T _ (⟦ σ ⟧s-cong₂ γsq) (⟦ σ ⟧s-cong₂ δsq) (⟦ σ ⟧s-cong₂ sq₁) (⟦ σ ⟧s-cong₂ sq₂) (⟦ σ ⟧s-cong₂ sqₑ) (⟦ σ ⟧s-cong₂ sqₑ')}

⟦ • ⟧s γ = lift ⊤.tt
⟦ σ ,,, t ⟧s γ = ⟦ σ ⟧s γ , ⟦ t ⟧⊢ γ

⟦ • ⟧s-cong _ = ⊤.tt
⟦ σ ,,, t ⟧s-cong γ* = (⟦ σ ⟧s-cong γ*) , ⟦ t ⟧⊢-cong γ*

⟦ • ⟧s-cong₂ _ = ⊤.tt
⟦ σ ,,, t ⟧s-cong₂ γ₂ = (⟦ σ ⟧s-cong₂ γ₂) , ⟦ t ⟧⊢-cong₂ γ₂

the-same : ∀ {Γ Δ m n} {S : Typeover m Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {t : Γ ⊢ TypeoverF σ S } → Γ ⊢ TypeoverF σ T → Γ ⊢ TypeoverF (_,,,_ {Γ} {m} {Δ} {S} σ t) (weak T) 
the-same x = {!x!}

apsub : ∀ {Γ Δ n} {T : Typeover n Δ} (σ : Sub Γ Δ) → Δ ∋ T → Γ ⊢ TypeoverF σ T
apsub {Γ} (_,,,_ {n} {Δ} {T} σ t) top = the-same {Γ} {Δ} {n} {n} {T} {T} {σ} {t} t
apsub {Γ} (_,,,_ {n} {Δ} {T} σ t) (pop .{n} {m} .{Δ} .{T} {S} x) = {!the-same {Γ} {Δ} {n} {T = T} {σ = σ} {t} ?!} -- apsub σ x

apsub-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {x : Δ ∋ T} {γ} → ⟦ apsub σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (⟦ σ ⟧s γ)
apsub-sound {σ = _ ,,, _} {x = top} = refl
apsub-sound {σ = _ ,,, _} {pop x} = apsub-sound {x = x}

sub : ∀ {n Γ Δ} {T : Typeover n Δ} (σ : Sub Γ Δ) → Δ ⊢ T → Γ ⊢ TypeoverF σ T
sub σ (VAR x) = apsub σ x
sub σ PRP = {!PRP!}
sub σ (REF t) = {!!}

sub-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σ : Sub Γ Δ} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ {!!} --⟦ t ⟧⊢ (⟦ σ ⟧s γ)
sub-sound {t = VAR x} = apsub-sound {x = x}
sub-sound {t = PRP} = refl
sub-sound {t = REF t} = {!!}

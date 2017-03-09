{-# OPTIONS --rewriting #-}
module Syntax where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import FibSetoid
open import Univ
open import Univ.HLevel
open import Context

--TODO Remove old equality constructions in Univ
--TODO Extract function for ap₂ ∘ Typeover.obj-cong T

--TODO Make "Vertex" and "Point" consistent

--TODO Move to Context.agda?
--TODO Make arguments to ap₃ (Typeover.obj-cong₂ T) implicit

data _⊢_∋_ (Γ : Cx) : ∀ {n} (T : Typeover n Γ) (t : Section T) → Set₁

data _⊢_∋_ Γ where

  VAR : ∀ {n} {T : Typeover n Γ} → 
      (x : Γ ∋ T) →
    -----------------
      Γ ⊢ T ∋ ⟦ x ⟧V

  PRP :
    ---------------------------------
      Γ ⊢ K hone Γ sets ∋ const prp

--TODO Better notation
--TODO Extract the type below
  REF : ∀ {n} {T : Typeover n Γ} {⟦t⟧}
      (t : Γ ⊢ T ∋ ⟦t⟧) →
    -----------------
      Γ ⊢ eqS ⟦t⟧ (refT T) ⟦t⟧ ∋ refS ⟦t⟧

  EQCONG : ∀ {n} {S S' T T' : Typeover n Γ}
           {E : EqT S S'} {E' : EqT T T'}
           {F : EqT S T} {F' : EqT S' T'}
           {⟦s⟧ : Section S} {⟦s'⟧ : Section S'} {⟦t⟧ : Section T} {⟦t'⟧ : Section T'}
           {⟦s*⟧ : Section (eqS ⟦s⟧ E ⟦s'⟧)} {⟦t*⟧ : Section (eqS ⟦t⟧ E' ⟦t'⟧)} →
           (s* : Γ ⊢ eqS ⟦s⟧ E ⟦s'⟧ ∋ ⟦s*⟧) (f* : Γ ⊢ {!!} ∋ {!!}) (t* : Γ ⊢ eqS ⟦t⟧ E' ⟦t'⟧ ∋ ⟦t*⟧) →
         --------------------------------------
           Γ ⊢ EqTypeover (eqS ⟦s⟧ F ⟦t⟧) (eqS ⟦s'⟧ F' ⟦t'⟧) ∋ {!!}

--TODO Make n explicit in refn, refn-cong

SectionF : ∀ {n Γ Δ} {T : Typeover n Δ} (F : OneTypeMap Γ Δ) → Section T → Section (TypeoverF F T)
SectionF F s = record {
  vertex = λ γ → Section.vertex s (app F γ) ;
  edge = λ γ* → Section.edge s (app₂ F γ*) ;
  face = λ sq-fill → Section.face s (app₃ F sq-fill) }

--A substitution or context morphism from Γ to Δ
--TODO Refactor
data Sub Γ : ∀ (Δ : Cx) (⟦σ⟧ : OneTypeMap Γ Δ) → Set₁ where
  • : Sub Γ ε (mkOneTypeFunctor (mkRefGraphFunctor (λ x → lift tt) (λ x₁ → tt)) (λ x → tt))
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) {⟦t⟧} (t : Γ ⊢ TypeoverF ⟦σ⟧ T ∋ ⟦t⟧) → Sub Γ (Δ ,, T) (mkOneTypeFunctor (mkRefGraphFunctor
    (λ γ → (app ⟦σ⟧ γ) , (Section.vertex ⟦t⟧ γ))
    (λ γ* → (app₂ ⟦σ⟧ γ*) , (Section.edge ⟦t⟧ γ*)))
    (λ sq-fill → (app₃ ⟦σ⟧ sq-fill) , (Section.face ⟦t⟧ sq-fill)))

ap : ∀ {Γ Δ n} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) (x : Δ ∋ T) →
  Γ ⊢ TypeoverF ⟦σ⟧ T ∋
    record { vertex = λ γ → ⟦ x ⟧∋ (app ⟦σ⟧ γ);
    edge = λ {γ γ'} (γ* : EQC Γ γ γ') → ⟦ x ⟧∋-cong (app₂ ⟦σ⟧ γ*);
    face = λ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
      (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') → ⟦ x ⟧∋-cong₂ (app₃ ⟦σ⟧ sq-fill) }
ap (σ ,,, t) top = t
ap (σ ,,, t) (pop x) = ap σ x

sub : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) {⟦t⟧} →
  Δ ⊢ T ∋ ⟦t⟧ → Γ ⊢ TypeoverF ⟦σ⟧ T ∋ SectionF ⟦σ⟧ ⟦t⟧
sub σ (VAR x) = ap σ x
sub σ PRP = PRP
sub σ (REF t) = REF (sub σ t)
sub σ (EQCONG s* f* t*) = {!!}

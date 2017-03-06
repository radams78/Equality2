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

--TODO Move to Context.agda?
--TODO Make arguments to ap₃ (Typeover.obj-cong₂ T) implicit
record Section {n Γ} (T : Typeover n Γ) : Set₁ where
  field
    vertex : ∀ (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
    edge   : ∀ {γ γ'} (γ* : EQC Γ γ γ') → T ∋ vertex γ ∼⟨ γ* ⟩ vertex γ'
    face   : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'}
      {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
      [ pred n ] edge γ₁* ∼⟪ eqTTn-cong n (edge γₑ) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill) (edge γₑ') ⟫ edge γ₂*

⟦_⟧V : ∀ {n Γ} {T : Typeover n Γ} → (Γ ∋ T) → Section T
⟦ x ⟧V = record { vertex = ⟦ x ⟧∋ ; edge = ⟦ x ⟧∋-cong ; face = ⟦ x ⟧∋-cong₂ }

const : ∀ {n Γ} {A : Type n} (a : TT A) → Section (K n Γ A)
const {n} a = record {
  vertex = λ _ → a ;
  edge = λ _ → refn a ;
  face = λ _ → refn-cong {n} (refn a) }

record EqT {n Γ} (S T : Typeover n Γ) : Set₁ where
  field
    vertex : ∀ γ → Eq (Typeover.obj S γ) (Typeover.obj T γ)
    edge   : ∀ {γ γ'} (γ* : EQC Γ γ γ') →
      [ n ] vertex γ ∼⟪ eqn-cong (ap₂ (Typeover.obj-cong S) γ*) (ap₂ (Typeover.obj-cong T) γ*) ⟫ vertex γ'
    face   : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'}
      {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
      [ pred n ] edge γ₁* ∼⟪ eqTTn-cong n (edge γₑ) (eqn-cong₂ n (ap₃ (Typeover.obj-cong₂ S) γ₁* γ₂* γₑ γₑ' sq-fill)
        (ap₃ (Typeover.obj-cong₂ T) γ₁* γ₂* γₑ γₑ' sq-fill)) (edge γₑ') ⟫
        edge γ₂*

refT : ∀ {n Γ} (T : Typeover n Γ) → EqT T T
refT {n} {Γ} T = record {
  vertex = λ γ → Refn (Typeover.obj T γ) ;
  edge = λ γ* → Refn-cong (ap₂ (Typeover.obj-cong T) γ*) ;
  face = λ sq-fill → Refn-cong₂ {n} (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill) }

eqS : ∀ {n Γ} {S T : Typeover n Γ} → Section S → EqT S T → Section T → Typeover (pred n) Γ
eqS {n} {Γ} {S} {T} s e t = record {
  obj = λ γ → eqTTn (Section.vertex s γ) (EqT.vertex e γ) (Section.vertex t γ) ;
  obj-cong = make-Functor (λ γ* → eqTTn-cong n (Section.edge s γ*) (EqT.edge e γ*) (Section.edge t γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face s sq-fill) (EqT.face e sq-fill) (Section.face t sq-fill)) ;
  obj-cong₃ = trivial n }

refS : ∀ {n Γ} {T : Typeover n Γ} (s : Section T) → Section (eqS s (refT T) s)
refS {n} {Γ} {T} s = record {
  vertex = λ γ → refn (Section.vertex s γ) ;
  edge = λ γ* → refn-cong {n} (Section.edge s γ*) ;
  face = λ _ → trivial n }

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

--TODO Make n explicit in refn, refn-cong

--TODO Common pattern with Section?
record OneTypeMap (Γ Δ : Cx) : Set₁ where
  field
    vertex : ⟦ Γ ⟧C → ⟦ Δ ⟧C
    edge   : Functor' Γ Δ vertex
    face   : Functor₂' edge

record OneTypeMapEq {Γ Δ} (F G : OneTypeMap Γ Δ) : Set₁ where
  field
    vertex : ∀ γ → EQC Δ (OneTypeMap.vertex F γ) (OneTypeMap.vertex G γ)
    edge : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (vertex γ) (vertex γ') (ap₂' (OneTypeMap.edge F) γ*) (ap₂' (OneTypeMap.edge G) γ*)

TypeoverF : ∀ {n} {Γ Δ} → OneTypeMap Γ Δ → Typeover n Δ → Typeover n Γ
TypeoverF F T = record {
  obj = λ γ → Typeover.obj T (OneTypeMap.vertex F γ) ;
  obj-cong = make-Functor (λ γ* → ap₂ (Typeover.obj-cong T) (ap₂' (OneTypeMap.edge F) γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → ap₃ (Typeover.obj-cong₂ T) (ap₂' (OneTypeMap.edge F) γ₁*) (ap₂' (OneTypeMap.edge F) γ₂*) (ap₂' (OneTypeMap.edge F) γₑ) (ap₂' (OneTypeMap.edge F) γₑ') (ap₃' (OneTypeMap.face F) sq-fill)) ;
  obj-cong₃ = Typeover.obj-cong₃ T}

SectionF : ∀ {n Γ Δ} {T : Typeover n Δ} (F : OneTypeMap Γ Δ) → Section T → Section (TypeoverF F T)
SectionF F s = record {
  vertex = λ γ → Section.vertex s (OneTypeMap.vertex F γ) ;
  edge = λ γ* → Section.edge s (ap₂' (OneTypeMap.edge F) γ*) ;
  face = λ sq-fill → Section.face s (ap₃' (OneTypeMap.face F) sq-fill) }

--A substitution or context morphism from Γ to Δ
--TODO Refactor
data Sub Γ : ∀ (Δ : Cx) (⟦σ⟧ : OneTypeMap Γ Δ) → Set₁ where
  • : Sub Γ ε (record { vertex = λ _ → lift tt ; edge = make-Functor' (λ _ → tt) ; face = make-Functor₂' (λ _ → tt) })
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) {⟦t⟧} (t : Γ ⊢ TypeoverF ⟦σ⟧ T ∋ ⟦t⟧) → Sub Γ (Δ ,, T) (record {
    vertex = λ γ → OneTypeMap.vertex ⟦σ⟧ γ , Section.vertex ⟦t⟧ γ ;
    edge = make-Functor' (λ γ* → ap₂' (OneTypeMap.edge ⟦σ⟧) γ* , Section.edge ⟦t⟧ γ*) ;
    face = make-Functor₂' (λ sq-fill → (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill) , (Section.face ⟦t⟧ sq-fill))})

ap : ∀ {Γ Δ n} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) (x : Δ ∋ T) →
  Γ ⊢ TypeoverF ⟦σ⟧ T ∋
    record { vertex = λ γ → ⟦ x ⟧∋ (OneTypeMap.vertex ⟦σ⟧ γ);
    edge = λ {γ γ'} (γ* : EQC Γ γ γ') → ⟦ x ⟧∋-cong (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*);
    face = λ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
      (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') → ⟦ x ⟧∋-cong₂ (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill) }
ap (σ ,,, t) top = t
ap (σ ,,, t) (pop x) = ap σ x

sub : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) {⟦t⟧} →
  Δ ⊢ T ∋ ⟦t⟧ → Γ ⊢ TypeoverF ⟦σ⟧ T ∋ SectionF ⟦σ⟧ ⟦t⟧
sub σ (VAR x) = ap σ x
sub σ PRP = PRP
sub σ (REF t) = REF (sub σ t)

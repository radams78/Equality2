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

<<<<<<< HEAD
<<<<<<< HEAD
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
=======
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
--TODO Remove old equality constructions in Univ
--TODO Extract function for ap₂ ∘ Typeover.obj-cong T

--TODO Make "Vertex" and "Point" consistent

--TODO Move to Context.agda?
--TODO Make arguments to ap₃ (Typeover.obj-cong₂ T) implicit

data _⊢_∋_ (Γ : Cx) : ∀ {n} (T : Typeover n Γ) (t : Section T) → Set₁

<<<<<<< HEAD
data _⊢_∋_ Γ where
=======
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
<<<<<<< HEAD
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31

data _⊢_ (Γ : Cx) : ∀ {n} → Typeover n Γ → Set₁
⟦_⟧⊢ : ∀ {Γ n} {T : Typeover n Γ} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦_⟧⊢-cong : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ t ⟧⊢ γ ∼〈 γ* 〉 ⟦ t ⟧⊢ γ'
<<<<<<< HEAD
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
=======
⟦_⟧⊢-cong₂ : ∀ {Γ n} {T : Typeover n Γ} (t : Γ ⊢ T) {a₁ a₂ b₁ b₂}
  {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ pred n ] ⟦ t ⟧⊢-cong a* ∼⟪ eqTTn-cong n (⟦ t ⟧⊢-cong p₁) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) (⟦ t ⟧⊢-cong p₂) ⟫ ⟦ t ⟧⊢-cong b*
<<<<<<< HEAD
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31

data _⊢_ Γ where
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

  VAR : ∀ {n} {T : Typeover n Γ} → 
      (x : Γ ∋ T) →
    -----------------
      Γ ⊢ T ∋ ⟦ x ⟧V

  PRP :
    ---------------------------------
      Γ ⊢ K hone Γ sets ∋ const prp

<<<<<<< HEAD
--TODO Better notation
=======
<<<<<<< HEAD
<<<<<<< HEAD
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
=======
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062
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
<<<<<<< HEAD
sub σ (REF t) = REF (sub σ t)
sub σ (EQCONG s* f* t*) = {!!}
=======
sub .{pred n} {Γ} {_} σ (REF {n} {T} t) = {!REF!}

sub-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {σs} {σs-cong} {σs-cong₂} {σ : Sub Γ Δ σs σs-cong σs-cong₂} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (σs γ)
sub-sound {t = VAR x} = ap-sound {x = x}
sub-sound {t = PRP} = refl
sub-sound {t = REF t} = {!!}
<<<<<<< HEAD
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

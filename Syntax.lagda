\begin{code}
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

--TODO Make arguments to ap₃ (Typeover.obj-cong₂ T) implicit
\end{code}

%<*Typing>
\begin{code}
data _⊢_∋_ (Γ : Cx) : ∀ {n} (T : Typeover n Γ) (t : Section T) → Set₁ where
\end{code}
%</Typing>

\begin{code}
  VAR : ∀ {n} {T : Typeover n Γ} → 
      (x : Γ ∋ T) →
    -----------------
      Γ ⊢ T ∋ ⟦ x ⟧V

  PRP :
    ---------------------------------
      Γ ⊢ K hone Γ sets ∋ const prp

--TODO Better notation
  REF : ∀ {n} {T : Typeover n Γ} {⟦t⟧}
      (t : Γ ⊢ T ∋ ⟦t⟧) →
    -----------------
      Γ ⊢ eqS ⟦t⟧ (refT T) ⟦t⟧ ∋ refS ⟦t⟧

  REF-CONG : ∀ {n} {S T : Typeover n Γ} {⟦s⟧} {⟦e⟧} {⟦t⟧} {⟦p⟧}
    {s : Γ ⊢ S ∋ ⟦s⟧} {e : Γ ⊢ EqTypeover S T ∋ ⟦e⟧} {t : Γ ⊢ T ∋ ⟦t⟧} →
    (p : Γ ⊢ eqS ⟦s⟧ ⟦e⟧ ⟦t⟧ ∋ ⟦p⟧) →
    Γ ⊢ eqS (refS ⟦s⟧) (eqS-cong ⟦p⟧ (refS ⟦e⟧) ⟦p⟧) (refS ⟦t⟧) ∋ {!refS-cong!}

  EQCONG : ∀ {n} {S S' T T' : Typeover n Γ}
           {S* : EqT S S'} {T* : EqT T T'}
           {F : EqT S T} {F' : EqT S' T'}
           {⟦s⟧ : Section S} {⟦s'⟧ : Section S'} {⟦t⟧ : Section T} {⟦t'⟧ : Section T'}
           {⟦s*⟧ : Section (eqS ⟦s⟧ S* ⟦s'⟧)} {⟦t*⟧ : Section (eqS ⟦t⟧ T* ⟦t'⟧)} 
           {⟦f*⟧ : Section (eqS F (EqTypeover-cong {n} {Γ} {S} {S'} {T} {T'} S* T*) F')} →
           (s* : Γ ⊢ eqS ⟦s⟧ S* ⟦s'⟧ ∋ ⟦s*⟧) (f* : Γ ⊢ eqS F (EqTypeover-cong {n} {Γ} {S} {S'} {T} {T'} S* T*) F' ∋ ⟦f*⟧) (t* : Γ ⊢ eqS ⟦t⟧ T* ⟦t'⟧ ∋ ⟦t*⟧) →
         --------------------------------------
           Γ ⊢ EqTypeover (eqS ⟦s⟧ F ⟦t⟧) (eqS ⟦s'⟧ F' ⟦t'⟧) ∋ eqS-cong {n} {Γ} {S} {S'} {T} {T'} ⟦s*⟧ ⟦f*⟧ ⟦t*⟧

--TODO Make n explicit in refn, refn-cong

{- SectionF : ∀ {n Γ Δ} {T : Typeover n Δ} (F : TwoGraphMap Γ Δ) → Section T → Section (TypeoverF F T)
SectionF F s = record {
  vertex = λ γ → Section.vertex s (app F γ) ;
  edge = λ γ* → Section.edge s (app₂ F γ*) ;
  face = λ sq-fill → Section.face s (app₃ F sq-fill) }

--A substitution or context morphism from Γ to Δ
--TODO Refactor
data Sub Γ : ∀ (Δ : Cx) (⟦σ⟧ : TwoGraphMap Γ Δ) → Set₁ where
  • : Sub Γ ε (mkTwoGraphFunctor (mkRefGraphFunctor (λ x → lift tt) (λ x₁ → tt)) (λ x → tt))
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} {⟦σ⟧} (σ : Sub Γ Δ ⟦σ⟧) {⟦t⟧} (t : Γ ⊢ TypeoverF ⟦σ⟧ T ∋ ⟦t⟧) → Sub Γ (Δ ,, T) (mkTwoGraphFunctor (mkRefGraphFunctor
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
sub σ (REF-CONG p) = {!!}
sub .{pred n} {Γ} {Δ} {⟦σ⟧ = ⟦σ⟧} σ (EQCONG {n} {S} {S'} {T} {T'} {S*} {T*} {F} {F'} {⟦s⟧} {⟦s'⟧} {⟦t⟧} {⟦t'⟧} {⟦s*⟧} {⟦t*⟧} {⟦F*⟧} s* f* t*) =  
  EQCONG {Γ} {n} {TypeoverF ⟦σ⟧ S} {TypeoverF ⟦σ⟧ S'} {TypeoverF ⟦σ⟧ T} {TypeoverF ⟦σ⟧ T'}
    {SectionF ⟦σ⟧ S*} {SectionF ⟦σ⟧ T*} {SectionF ⟦σ⟧ F} {SectionF ⟦σ⟧ F'} 
    {SectionF ⟦σ⟧ ⟦s⟧} {SectionF ⟦σ⟧ ⟦s'⟧} {SectionF ⟦σ⟧ ⟦t⟧} {SectionF ⟦σ⟧ ⟦t'⟧}
    {SectionF ⟦σ⟧ ⟦s*⟧} {SectionF ⟦σ⟧ ⟦t*⟧} {SectionF ⟦σ⟧ ⟦F*⟧}
    (sub σ s*) (sub σ f*) (sub σ t*) -}
\end{code}

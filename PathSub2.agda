module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Univ
open import Univ.HLevel
open import Context
open import Syntax
open import PathSub

--Put in section
apps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρs ρs-cong ρs-cong₂ σs σs-cong σs-cong₂ τs}
  {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' ρs-cong γ*) (ap₂' σs-cong γ*)}
  {ρ : Sub Γ Δ ρs ρs-cong ρs-cong₂} {σ : Sub Γ Δ σs σs-cong σs-cong₂} (τ : PathSub ρ σ τs τs-cong) (x : Δ ∋ T) →
  Γ ⊢ Typeover-eq τ T
    (λ γ → ⟦ x ⟧∋ (ρs γ))
    (λ γ* → ⟦ x ⟧∋-cong (ap₂' ρs-cong γ*))
    (λ sq-fill → ⟦ x ⟧∋-cong₂ (ap₃' ρs-cong₂ sq-fill))
    (λ γ → ⟦ x ⟧∋ (σs γ))
    (λ γ* → ⟦ x ⟧∋-cong (ap₂' σs-cong γ*))
    (λ sq-fill → ⟦ x ⟧∋-cong₂ (ap₃' σs-cong₂ sq-fill)) ∋ record {
      vertex = λ γ → ⟦ x ⟧∋-cong (τs γ) ;
      edge = λ γ* → ⟦ x ⟧∋-cong₂ (τs-cong γ*) ;
      face = λ sq-fill → trivial n }
apps (_ ,,, t*) top = t*
apps (τ ,,, _) (pop x) = apps τ x

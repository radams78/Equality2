module PathSub3 where
open import Univ.HLevel
open import Context
open import Syntax
open import PathSub
open import PathSub2

--Common pattern with apps
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρs ρs-cong ρs-cong₂ σs σs-cong σs-cong₂ τs}
  {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' ρs-cong γ*) (ap₂' σs-cong γ*)}
  {ρ : Sub Γ Δ ρs ρs-cong ρs-cong₂} {σ : Sub Γ Δ σs σs-cong σs-cong₂} (τ : PathSub ρ σ τs τs-cong)
  {⟦t⟧} (t : Δ ⊢ T ∋ ⟦t⟧) →
  Γ ⊢ Typeover-eq τ T
    (λ γ → Section.vertex ⟦t⟧ (ρs γ))
    (λ γ* → Section.edge ⟦t⟧ (ap₂' ρs-cong γ*))
    (λ sq-fill → Section.face ⟦t⟧ (ap₃' ρs-cong₂ sq-fill))
    (λ γ → Section.vertex ⟦t⟧ (σs γ))
    (λ γ* → Section.edge ⟦t⟧ (ap₂' σs-cong γ*))
    (λ sq-fill → Section.face ⟦t⟧ (ap₃' σs-cong₂ sq-fill)) ∋ record {
      vertex = λ γ → Section.edge ⟦t⟧ (τs γ) ;
      edge = λ γ* → Section.face ⟦t⟧ (τs-cong γ*) ;
      face = λ sq-fill → trivial n }
subps τ (VAR x) = apps τ x
subps τ PRP = REF PRP
subps τ (REF t) = {!!}

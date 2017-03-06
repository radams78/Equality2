module PathSub3 where
open import Univ.HLevel
open import Context
open import Syntax
open import PathSub
open import PathSub2

--TODO Common pattern with apps
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ τs}
  {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*)}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} (τ : PathSub ρ σ τs τs-cong)
  {⟦t⟧} (t : Δ ⊢ T ∋ ⟦t⟧) →
  Γ ⊢ Typeover-eq τ T
    (λ γ → Section.vertex ⟦t⟧ (OneTypeMap.vertex ⟦ρ⟧ γ))
    (λ γ* → Section.edge ⟦t⟧ (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*))
    (λ sq-fill → Section.face ⟦t⟧ (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill))
    (λ γ → Section.vertex ⟦t⟧ (OneTypeMap.vertex ⟦σ⟧ γ))
    (λ γ* → Section.edge ⟦t⟧ (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*))
    (λ sq-fill → Section.face ⟦t⟧ (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill)) ∋ record {
      vertex = λ γ → Section.edge ⟦t⟧ (τs γ) ;
      edge = λ γ* → Section.face ⟦t⟧ (τs-cong γ*) ;
      face = λ sq-fill → trivial n }
subps τ (VAR x) = apps τ x
subps τ PRP = REF PRP
subps τ (REF t) = {!!}

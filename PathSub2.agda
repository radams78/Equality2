module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Univ
open import Context
open import Syntax
open import PathSub

--Put in section
apps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ τs}
  {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*)}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} (τ : PathSub ρ σ τs τs-cong) (x : Δ ∋ T) →
  Γ ⊢ Typeover-eq {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} {τs} {τs-cong} T (record {
    vertex = λ γ → ⟦ x ⟧∋ (OneTypeMap.vertex ⟦ρ⟧ γ) ;
    edge = λ γ* → ⟦ x ⟧∋-cong (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) ;
    face = λ sq-fill → ⟦ x ⟧∋-cong₂ (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill) })
    (record {
    vertex = λ γ → ⟦ x ⟧∋ (OneTypeMap.vertex ⟦σ⟧ γ) ;
    edge = λ γ* → ⟦ x ⟧∋-cong (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*) ;
    face = λ sq-fill → ⟦ x ⟧∋-cong₂ (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill) }) ∋ 
    record {
      vertex = λ γ → ⟦ x ⟧∋-cong (τs γ) ;
      edge = λ γ* → ⟦ x ⟧∋-cong₂ (τs-cong γ*) ;
      face = λ sq-fill → trivial n }
apps (_ ,,, t*) top = t*
apps (τ ,,, _) (pop x) = apps τ x

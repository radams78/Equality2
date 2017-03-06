module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Univ
open import Context
open import Syntax
open import PathSub

--Put in section
apps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ ⟦τ⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} (τ : PathSub ρ σ ⟦τ⟧) (x : Δ ∋ T) →
  Γ ⊢ Typeover-eq {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ (record {
    vertex = λ γ → ⟦ x ⟧∋ (OneTypeMap.vertex ⟦ρ⟧ γ) ;
    edge = λ γ* → ⟦ x ⟧∋-cong (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) ;
    face = λ sq-fill → ⟦ x ⟧∋-cong₂ (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill) })
    (record {
    vertex = λ γ → ⟦ x ⟧∋ (OneTypeMap.vertex ⟦σ⟧ γ) ;
    edge = λ γ* → ⟦ x ⟧∋-cong (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*) ;
    face = λ sq-fill → ⟦ x ⟧∋-cong₂ (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill) }) ∋ 
    record {
      vertex = λ γ → ⟦ x ⟧∋-cong (OneTypeMapEq.vertex ⟦τ⟧ γ) ;
      edge = λ γ* → ⟦ x ⟧∋-cong₂ (OneTypeMapEq.edge ⟦τ⟧ γ*) ;
      face = λ sq-fill → trivial n }
apps (_ ,,, t*) top = t*
apps (τ ,,, _) (pop x) = apps τ x

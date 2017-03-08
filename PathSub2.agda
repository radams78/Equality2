module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Univ
open import Context
open import Syntax
open import Substitution
open import PathSub

apps-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} {τ : PathSub ρ σ} {x : Δ ∋ T} {γ} → ⟦ apps τ x ⟧⊢ γ ≡ ⟦ x ⟧∋-cong (⟦ τ ⟧ps γ)
apps-sound {ρ = •} {x = ()}
apps-sound {T = record { obj = _ ; obj-cong = _ ; obj-cong₂ = _ ; obj-cong₃ = _ }} {ρ ,,, s} {σ ,,, t} {τ ,,, p} {top} = refl
apps-sound {T = record { obj = _ ; obj-cong = _ ; obj-cong₂ = _ ; obj-cong₃ = _ }} {ρ ,,, s} {σ ,,, t} {τ ,,, p} {pop x} = apps-sound {ρ = ρ} {σ} {τ} {x}

subps : ∀ n {Γ Δ} (T : Typeover n Δ) (ρ σ : Sub Γ Δ) (τ : PathSub ρ σ) (t : Δ ⊢ T) → 
  Γ ⊢ TypeoverFF n ρ σ T (λ γ → ⟦ t ⟧⊢ (⟦ ρ ⟧s γ)) (λ γ* → ⟦ t ⟧⊢-cong (⟦ ρ ⟧s-cong γ*)) (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill)) τ 
  (λ γ → ⟦ t ⟧⊢ (⟦ σ ⟧s γ)) (λ γ* → ⟦ t ⟧⊢-cong (⟦ σ ⟧s-cong γ*)) (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ σ ⟧s-cong₂ sq-fill))
subps n T ρ σ τ (VAR x) = apps τ x
subps hone {Δ = Δ} .(K hone Δ sets) ρ σ τ PRP = {!!}

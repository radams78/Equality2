module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Univ
open import Context
open import Syntax
open import PathSub

--Put in section
apps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) →
  Γ ⊢ Typeover-eq τ T
    (λ γ → ⟦ x ⟧∋ (⟦ ρ ⟧s γ))
    (λ γ* → ⟦ x ⟧∋-cong (⟦ ρ ⟧s-cong γ*))
    (λ sq-fill → ⟦ x ⟧∋-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill))
    (λ γ → ⟦ x ⟧∋ (⟦ σ ⟧s γ))
    (λ γ* → ⟦ x ⟧∋-cong (⟦ σ ⟧s-cong γ*))
    (λ sq-fill → ⟦ x ⟧∋-cong₂ (⟦ σ ⟧s-cong₂ sq-fill))
apps (_ ,,, t) top = t
apps (τ ,,, _) (pop x) = apps τ x

apps-cong : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) γ →
  ⟦ apps τ x ⟧⊢ γ ≡ ⟦ x ⟧∋-cong (⟦ τ ⟧ps γ)
apps-cong (_ ,,, _) top _ = refl
apps-cong (τ ,,, _) (pop x) γ = apps-cong τ x γ

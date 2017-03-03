module PathSub3 where

--Common pattern with apps
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (t : Δ ⊢ T) →
  Γ ⊢ Typeover-eq τ T
    (λ γ → ⟦ t ⟧⊢ (⟦ ρ ⟧s γ))
    (λ γ* → ⟦ t ⟧⊢-cong (⟦ ρ ⟧s-cong γ*))
    (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill))
    (λ γ → ⟦ t ⟧⊢ (⟦ σ ⟧s γ))
    (λ γ* → ⟦ t ⟧⊢-cong (⟦ σ ⟧s-cong γ*))
    (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ σ ⟧s-cong₂ sq-fill))
subps τ t = ?

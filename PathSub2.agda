module PathSub2 where
open import Univ
open import Context
open import Syntax
open import PathSub

--Common pattern with df of PathSub?
{- apps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) →
  Γ ⊢ record {
    obj = λ γ → eqTTn (⟦ x ⟧∋ (⟦ ρ ⟧s γ)) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (⟦ x ⟧∋ (⟦ σ ⟧s γ)) ;
    obj-cong = λ γ* → eqTTn-cong n (⟦ x ⟧∋-cong (⟦ ρ ⟧s-cong γ*)) (Typeover.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (⟦ x ⟧∋-cong (⟦ σ ⟧s-cong γ*)) ;
    obj-cong₂ = λ sq-fill → eqTTn-cong₂ {n} (⟦ x ⟧∋-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill)) (Typeover.obj-cong₃ T (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ ρ ⟧s-cong₂ sq-fill) (⟦ σ ⟧s-cong₂ sq-fill)) (⟦ x ⟧∋-cong₂ (⟦ σ ⟧s-cong₂ sq-fill)) ;
    obj-cong₃ = λ _ _ _ _ _ _ → trivial n }
apps (τ ,,, t) top = t
apps (τ ,,, t) (pop x) = apps τ x -}

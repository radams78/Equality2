<<<<<<< HEAD
<<<<<<< HEAD
open import Univ
open import Context
open import Substitution
open import PathSub

=======
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
module PathSub3 where
open import Univ.HLevel
open import Context
open import Syntax
open import PathSub
open import PathSub2

<<<<<<< HEAD
=======
--Common pattern with apps
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (t : Δ ⊢ T) →
  Γ ⊢ Typeover-eq τ T
    (λ γ → ⟦ t ⟧⊢ (⟦ ρ ⟧s γ))
    (λ γ* → ⟦ t ⟧⊢-cong (⟦ ρ ⟧s-cong γ*))
    (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill))
    (λ γ → ⟦ t ⟧⊢ (⟦ σ ⟧s γ))
    (λ γ* → ⟦ t ⟧⊢-cong (⟦ σ ⟧s-cong γ*))
    (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ σ ⟧s-cong₂ sq-fill))
subps τ (VAR x) = apps τ x
subps τ PRP = {!!}
<<<<<<< HEAD
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

module PathSub3 where
open import Univ.HLevel
open import Context
open import Syntax
open import PathSub
open import PathSub2

--TODO Common pattern with apps
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ ⟦τ⟧ ⟦t⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} → PathSub ρ σ ⟦τ⟧ → Δ ⊢ T ∋ ⟦t⟧ →
  Γ ⊢ Typeover-eq {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ (SectionF ⟦ρ⟧ ⟦t⟧) (SectionF ⟦σ⟧ ⟦t⟧) ∋ SectionF₂ ⟦τ⟧ ⟦t⟧
subps τ (VAR x) = apps τ x
subps τ PRP = REF PRP
subps τ (REF t) = {!!}

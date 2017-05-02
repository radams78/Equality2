module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Univ
open import Context
open import Syntax
open import PathSub

apps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ ⟦τ⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} (τ : PathSub ρ σ ⟦τ⟧) (x : Δ ∋ T) →
  Γ ⊢ Typeover-eq {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ (SectionF ⟦ρ⟧ ⟦ x ⟧V) (SectionF ⟦σ⟧ ⟦ x ⟧V) ∋ SectionF₂ ⟦τ⟧ ⟦ x ⟧V
apps (_ ,,, t*) top = t*
apps (τ ,,, _) (pop x) = apps τ x

subps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ ⟦τ⟧ ⟦t⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} → PathSub ρ σ ⟦τ⟧ → Δ ⊢ T ∋ ⟦t⟧ →
  Γ ⊢ Typeover-eq T ⟦τ⟧ (SectionF ⟦ρ⟧ ⟦t⟧) (SectionF ⟦σ⟧ ⟦t⟧) ∋ SectionF₂ ⟦τ⟧ ⟦t⟧
subps τ (VAR x) = apps τ x
subps τ PRP = REF PRP
subps τ (REF t) = {!REF!}
subps τ (EQCONG s* f* t*) = {!!}

module PathSub3 where
open import Univ.HLevel
open import Context
open import Syntax
open import PathSub
open import PathSub2

record OneTypeMapEq {Γ Δ} (F G : OneTypeMap Γ Δ) : Set₁ where
  field
    vertex : ∀ γ → EQC Δ (OneTypeMap.vertex F γ) (OneTypeMap.vertex G γ)
    edge : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (vertex γ) (vertex γ') (ap₂' (OneTypeMap.edge F) γ*) (ap₂' (OneTypeMap.edge G) γ*)

SectionF₂ : ∀ {n Γ Δ} {F G : OneTypeMap Γ Δ} {T : Typeover n Δ} (P : OneTypeMapEq F G) (s : Section T) →
  Section (Typeover-eq {⟦ρ⟧ = F} {G} {OneTypeMapEq.vertex P} {OneTypeMapEq.edge P} T (SectionF F s) (SectionF G s))
SectionF₂ {n} {Γ} {Δ} {F} {G} {T} P s = record {
  vertex = λ γ → Section.edge s (OneTypeMapEq.vertex P γ) ;
  edge = λ γ* → Section.face s (OneTypeMapEq.edge P γ*) ;
  face = λ _ → trivial n }

--TODO Common pattern with apps
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧} {⟦τ⟧ : OneTypeMapEq ⟦ρ⟧ ⟦σ⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} (τ : PathSub ρ σ (OneTypeMapEq.vertex ⟦τ⟧) (OneTypeMapEq.edge ⟦τ⟧))
  {⟦t⟧} (t : Δ ⊢ T ∋ ⟦t⟧) →
  Γ ⊢ Typeover-eq {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} {OneTypeMapEq.vertex ⟦τ⟧} {OneTypeMapEq.edge ⟦τ⟧} T (SectionF ⟦ρ⟧ ⟦t⟧) (SectionF ⟦σ⟧ ⟦t⟧) ∋ SectionF₂ ⟦τ⟧ ⟦t⟧
subps τ (VAR x) = apps τ x
subps τ PRP = REF PRP
subps τ (REF t) = {!!}

module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax

Typeover-eq : ∀ {n Γ Δ ⟦ρ⟧ ⟦σ⟧} (T : Typeover n Δ) →
  OneTypeMapEq ⟦ρ⟧ ⟦σ⟧ →
  (F : Section (TypeoverF ⟦ρ⟧ T))
  (G : Section (TypeoverF ⟦σ⟧ T)) →
  Typeover (pred n) Γ
Typeover-eq {n} {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ F G = record {
  obj = λ γ → eqTTn (Section.vertex F γ) (ap₂ (Typeover.obj-cong T) (OneTypeMapEq.vertex ⟦τ⟧ γ)) (Section.vertex G γ) ;
  obj-cong = make-Functor (λ {γ} {γ'} γ* → eqTTn-cong n (Section.edge F γ*) (ap₃ (Typeover.obj-cong₂ T) (OneTypeMapEq.vertex ⟦τ⟧ _) (OneTypeMapEq.vertex ⟦τ⟧ _) (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*) (OneTypeMapEq.edge ⟦τ⟧ γ*)) (Section.edge G γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face F sq-fill) (Typeover.obj-cong₃ T (OneTypeMapEq.edge ⟦τ⟧ γ₁*) (OneTypeMapEq.edge ⟦τ⟧ γ₂*) (OneTypeMapEq.edge ⟦τ⟧ γₑ) (OneTypeMapEq.edge ⟦τ⟧ γₑ') (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill) (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill)) (Section.face G sq-fill)) ;
  obj-cong₃' = trivial n }

SectionF₂ : ∀ {n Γ Δ} {F G : OneTypeMap Γ Δ} {T : Typeover n Δ} (P : OneTypeMapEq F G) (s : Section T) →
  Section (Typeover-eq {⟦ρ⟧ = F} {G} T P (SectionF F s) (SectionF G s))
SectionF₂ {n} {Γ} {Δ} {F} {G} {T} P s = record {
  vertex = λ γ → Section.edge s (OneTypeMapEq.vertex P γ) ;
  edge = λ γ* → Section.face s (OneTypeMapEq.edge P γ*) ;
  face = λ _ → trivial n }

--Make n explicit in eqTTn-cong₂
--Extract notion of section
--TODO Type for τs and OneTypeMapEq.edge ⟦τ⟧ combined
data PathSub {Γ} : ∀ {Δ ⟦ρ⟧ ⟦σ⟧}
  (ρ : Sub Γ Δ ⟦ρ⟧) (σ : Sub Γ Δ ⟦σ⟧) →
  OneTypeMapEq ⟦ρ⟧ ⟦σ⟧
  → Set₁ where
  • : PathSub • • (record { vertex = λ γ → tt ; edge = λ γ* → tt })
  _,,,_ : ∀ {n Δ ⟦ρ⟧ ⟦σ⟧ ⟦τ⟧}
    {T : Typeover n Δ}
    {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧}
    {⟦s⟧ : Section (TypeoverF ⟦ρ⟧ T)}
    {⟦t⟧ : Section (TypeoverF ⟦σ⟧ T)}
    (τ : PathSub ρ σ ⟦τ⟧)
    {s : Γ ⊢ _ ∋ ⟦s⟧} {t : Γ ⊢ _ ∋ ⟦t⟧}
    {s-is-t : ∀ γ → [ n ] Section.vertex ⟦s⟧ γ ∼⟪ ap₂ (Typeover.obj-cong T) (OneTypeMapEq.vertex ⟦τ⟧ γ) ⟫ Section.vertex ⟦t⟧ γ }
    {s-is-t-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ pred n ] s-is-t γ ∼⟪ eqTTn-cong n (Section.edge ⟦s⟧ γ*) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ (OneTypeMapEq.edge ⟦τ⟧ γ*)) (Section.edge ⟦t⟧ γ*) ⟫ s-is-t γ'} →
      Γ ⊢ Typeover-eq {n} {Γ} {Δ} {⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ ⟦s⟧ ⟦t⟧ ∋ record { vertex = s-is-t; edge = s-is-t-cong; face = λ _ → trivial n } →
      PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t) (record { vertex = λ γ → (OneTypeMapEq.vertex ⟦τ⟧ γ) , s-is-t γ;
      edge = λ γ* → (OneTypeMapEq.edge ⟦τ⟧ γ*) , s-is-t-cong γ* })


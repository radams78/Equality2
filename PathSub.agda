module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax

Typeover-eq : ∀ {n Γ Δ ⟦ρ⟧ ⟦σ⟧} {τs : ∀ γ → EQC Δ (OneTypeMap.vertex ⟦ρ⟧ γ) (OneTypeMap.vertex ⟦σ⟧ γ)}
  {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*)}
  (T : Typeover n Δ)
  (F : Section (TypeoverF ⟦ρ⟧ T))
  (G : Section (TypeoverF ⟦σ⟧ T)) →
  Typeover (pred n) Γ
Typeover-eq {n} {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} {τs = τs} {τs-cong} T F G = record {
  obj = λ γ → eqTTn (Section.vertex F γ) (ap₂ (Typeover.obj-cong T) (τs γ)) (Section.vertex G γ) ;
  obj-cong = make-Functor (λ {γ} {γ'} γ* → eqTTn-cong n (Section.edge F γ*) (ap₃ (Typeover.obj-cong₂ T) (τs _) (τs _) (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*) (τs-cong γ*)) (Section.edge G γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face F sq-fill) (Typeover.obj-cong₃ T (τs-cong γ₁*) (τs-cong γ₂*) (τs-cong γₑ) (τs-cong γₑ') (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill) (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill)) (Section.face G sq-fill)) ;
  obj-cong₃' = trivial n }

SectionF₂ : ∀ {n Γ Δ} {F G : OneTypeMap Γ Δ} {T : Typeover n Δ} (P : OneTypeMapEq F G) (s : Section T) →
  Section (Typeover-eq {⟦ρ⟧ = F} {G} {OneTypeMapEq.vertex P} {OneTypeMapEq.edge P} T (SectionF F s) (SectionF G s))
SectionF₂ {n} {Γ} {Δ} {F} {G} {T} P s = record {
  vertex = λ γ → Section.edge s (OneTypeMapEq.vertex P γ) ;
  edge = λ γ* → Section.face s (OneTypeMapEq.edge P γ*) ;
  face = λ _ → trivial n }

--Make n explicit in eqTTn-cong₂
--Extract notion of section
--TODO Type for τs and τs-cong combined
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
      Γ ⊢ Typeover-eq {n} {Γ} {Δ} {⟦ρ⟧} {⟦σ⟧} {τs = OneTypeMapEq.vertex ⟦τ⟧} {τs-cong = OneTypeMapEq.edge ⟦τ⟧} T ⟦s⟧ ⟦t⟧ ∋ record { vertex = s-is-t; edge = s-is-t-cong; face = λ _ → trivial n } →
      PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t) (record { vertex = λ γ → (OneTypeMapEq.vertex ⟦τ⟧ γ) , s-is-t γ;
      edge = λ γ* → (OneTypeMapEq.edge ⟦τ⟧ γ*) , s-is-t-cong γ* })


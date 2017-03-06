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

--Make n explicit in eqTTn-cong₂
--Extract notion of section
--TODO Type for τs and τs-cong combined
data PathSub {Γ} : ∀ {Δ ⟦ρ⟧ ⟦σ⟧}
  (ρ : Sub Γ Δ ⟦ρ⟧) (σ : Sub Γ Δ ⟦σ⟧)
  (τs : ∀ γ → EQC Δ (OneTypeMap.vertex ⟦ρ⟧ γ) (OneTypeMap.vertex ⟦σ⟧ γ))
  (τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*))
  → Set₁ where
  • : PathSub • • (λ _ → tt) (λ _ → tt)
  _,,,_ : ∀ {n Δ ⟦ρ⟧ ⟦σ⟧ τs}
    {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*)}
    {T : Typeover n Δ}
    {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧}
    {⟦s⟧ : Section (TypeoverF ⟦ρ⟧ T)}
    {⟦t⟧ : Section (TypeoverF ⟦σ⟧ T)}
    (τ : PathSub ρ σ τs τs-cong)
    {s : Γ ⊢ _ ∋ ⟦s⟧} {t : Γ ⊢ _ ∋ ⟦t⟧}
    {s-is-t : ∀ γ → [ n ] Section.vertex ⟦s⟧ γ ∼⟪ ap₂ (Typeover.obj-cong T) (τs γ) ⟫ Section.vertex ⟦t⟧ γ }
    {s-is-t-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ pred n ] s-is-t γ ∼⟪ eqTTn-cong n (Section.edge ⟦s⟧ γ*) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ (τs-cong γ*)) (Section.edge ⟦t⟧ γ*) ⟫ s-is-t γ'} →
      Γ ⊢ Typeover-eq {n} {Γ} {Δ} {⟦ρ⟧} {⟦σ⟧} {τs = τs} {τs-cong = τs-cong} T ⟦s⟧ ⟦t⟧ ∋ record { vertex = s-is-t; edge = s-is-t-cong; face = λ _ → trivial n } →
      PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t) (λ γ → (τs γ) , s-is-t γ) (λ γ* → (τs-cong γ*) , s-is-t-cong γ*)


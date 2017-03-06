module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax


--Make n explicit in eqTTn-cong₂
--Extract notion of section
--TODO Type for τs and τs-cong combined
data PathSub {Γ} : ∀ {Δ ⟦ρ⟧ ⟦σ⟧}
  (ρ : Sub Γ Δ ⟦ρ⟧) (σ : Sub Γ Δ ⟦σ⟧)
  (τs : ∀ γ → EQC Δ (OneTypeMap.vertex ⟦ρ⟧ γ) (OneTypeMap.vertex ⟦σ⟧ γ))
  (τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*))
  → Set₁
Typeover-eq : ∀ {n Γ Δ ⟦ρ⟧ ⟦σ⟧ τs}
  {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*)}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧}
  (τ : PathSub ρ σ τs τs-cong) (T : Typeover n Δ)
  (F : ∀ γ → ⟦ T ⟧T (OneTypeMap.vertex ⟦ρ⟧ γ))
  (F-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ n ] F γ ∼⟪ ap₂ (Typeover.obj-cong T) (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) ⟫ F γ')
  (F-cong₂ : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
    [ pred n ] F-cong γ₁* ∼⟪ eqTTn-cong n (F-cong γₑ) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill)) (F-cong γₑ') ⟫ F-cong γ₂*)
  (G : ∀ γ → ⟦ T ⟧T (OneTypeMap.vertex ⟦σ⟧ γ))
  (G-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ n ] G γ ∼⟪ ap₂ (Typeover.obj-cong T) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*) ⟫ G γ') →
  (G-cong₂ : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
    [ pred n ] G-cong γ₁* ∼⟪ eqTTn-cong n (G-cong γₑ) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill)) (G-cong γₑ') ⟫ G-cong γ₂*) →
  Typeover (pred n) Γ

Typeover-eq {n} {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} {τs = τs} {τs-cong} τ T F F-cong F-cong₂ G G-cong G-cong₂ = record {
  obj = λ γ → eqTTn (F γ) (ap₂ (Typeover.obj-cong T) (τs γ)) (G γ) ;
  obj-cong = make-Functor (λ {γ} {γ'} γ* → eqTTn-cong n (F-cong γ*) (ap₃ (Typeover.obj-cong₂ T) (τs _) (τs _) (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*) (τs-cong γ*)) (G-cong γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (F-cong₂ sq-fill) (Typeover.obj-cong₃ T (τs-cong γ₁*) (τs-cong γ₂*) (τs-cong γₑ) (τs-cong γₑ') (ap₃' (OneTypeMap.face ⟦ρ⟧) sq-fill) (ap₃' (OneTypeMap.face ⟦σ⟧) sq-fill)) (G-cong₂ sq-fill)) ;
  obj-cong₃' = trivial n }

data PathSub {Γ} where
  • : PathSub • • (λ _ → tt) (λ _ → tt)
  _,,,_ : ∀ {n Δ ⟦ρ⟧ ⟦σ⟧ τs}
    {τs-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (τs γ) (τs γ') (ap₂' (OneTypeMap.edge ⟦ρ⟧) γ*) (ap₂' (OneTypeMap.edge ⟦σ⟧) γ*)}
    {T : Typeover n Δ}
    {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧}
    {⟦s⟧ : Section (TypeoverF (OneTypeMap.vertex ⟦ρ⟧) (OneTypeMap.edge ⟦ρ⟧) (OneTypeMap.face ⟦ρ⟧) T)}
    {⟦t⟧ : Section (TypeoverF (OneTypeMap.vertex ⟦σ⟧) (OneTypeMap.edge ⟦σ⟧) (OneTypeMap.face ⟦σ⟧) T)}
    (τ : PathSub ρ σ τs τs-cong)
    {s : Γ ⊢ _ ∋ ⟦s⟧} {t : Γ ⊢ _ ∋ ⟦t⟧}
    {s-is-t : ∀ γ → [ n ] Section.vertex ⟦s⟧ γ ∼⟪ ap₂ (Typeover.obj-cong T) (τs γ) ⟫ Section.vertex ⟦t⟧ γ }
    {s-is-t-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ pred n ] s-is-t γ ∼⟪ eqTTn-cong n (Section.edge ⟦s⟧ γ*) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ (τs-cong γ*)) (Section.edge ⟦t⟧ γ*) ⟫ s-is-t γ'} →
      Γ ⊢ Typeover-eq τ T (Section.vertex ⟦s⟧) (Section.edge ⟦s⟧) (Section.face ⟦s⟧) (Section.vertex ⟦t⟧) (Section.edge ⟦t⟧) (Section.face ⟦t⟧) ∋ record { vertex = s-is-t; edge = s-is-t-cong; face = λ _ → trivial n } →
      PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t) (λ γ → (τs γ) , s-is-t γ) (λ γ* → (τs-cong γ*) , s-is-t-cong γ*)


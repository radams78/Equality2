module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax

data PathSub {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
Typeover-eq : ∀ {n Γ Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (T : Typeover n Δ)
  (F : ∀ γ → ⟦ T ⟧T (⟦ ρ ⟧s γ))
  (F-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ n ] F γ ∼⟪ Typeover.obj-cong T (⟦ ρ ⟧s-cong γ*) ⟫ F γ')
  (F-cong₂ : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
    [ pred n ] F-cong γ₁* ∼⟪ eqTTn-cong n (F-cong γₑ) (Typeover.obj-cong₂ T (⟦ ρ ⟧s-cong₂ sq-fill)) (F-cong γₑ') ⟫ F-cong γ₂*)
  (G : ∀ γ → ⟦ T ⟧T (⟦ σ ⟧s γ))
  (G-cong : ∀ {γ γ'} (γ* : EQC Γ γ γ') → [ n ] G γ ∼⟪ Typeover.obj-cong T (⟦ σ ⟧s-cong γ*) ⟫ G γ') →
  (G-cong₂ : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'}
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
    [ pred n ] G-cong γ₁* ∼⟪ eqTTn-cong n (G-cong γₑ) (Typeover.obj-cong₂ T (⟦ σ ⟧s-cong₂ sq-fill)) (G-cong γₑ') ⟫ G-cong γ₂*) →
  Typeover (pred n) Γ
⟦_⟧ps : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)
⟦_⟧ps-cong : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) {γ γ'} (γ* : EQC Γ γ γ') →
  EQC₂ {Δ} (⟦ τ ⟧ps γ) (⟦ τ ⟧ps γ') (⟦ ρ ⟧s-cong γ*) (⟦ σ ⟧s-cong γ*)

--Make n explicit in eqTTn-cong₂
--Extract notion of section
data PathSub {Γ} where
  • : PathSub • •
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → Γ ⊢ Typeover-eq τ T ⟦ s ⟧⊢ ⟦ s ⟧⊢-cong ⟦ s ⟧⊢-cong₂ ⟦ t ⟧⊢ ⟦ t ⟧⊢-cong ⟦ t ⟧⊢-cong₂ →
       PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t)

Typeover-eq {n} {Γ} {Δ} {ρ} {σ} τ T F F-cong F-cong₂ G G-cong G-cong₂ = record {
  obj = λ γ → eqTTn (F γ) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (G γ) ;
  obj-cong = λ γ* → eqTTn-cong n (F-cong γ*) (Typeover.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (G-cong γ*) ;
  obj-cong₂ = λ γ₂ → eqTTn-cong₂ n (F-cong₂ γ₂) (Typeover.obj-cong₃ T (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ ρ ⟧s-cong₂ γ₂) (⟦ σ ⟧s-cong₂ γ₂)) (G-cong₂ γ₂) ;
  obj-cong₃ = λ _ _ _ _ _ _ → trivial n }

⟦ • ⟧ps γ = ⊤.tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , ⟦ b* ⟧⊢ γ

⟦ • ⟧ps-cong γ* = ⊤.tt
⟦ τ ,,, b* ⟧ps-cong γ* = (⟦ τ ⟧ps-cong γ*) , (⟦ b* ⟧⊢-cong γ*)

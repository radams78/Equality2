module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax

--Put in module with Γ Δ params
data PathSub {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
⟦_⟧ps : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)
⟦_⟧ps-cong : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) {γ γ'} (γ* : EQC Γ γ γ') →
  EQC₂ {Δ} (⟦ τ ⟧ps γ) (⟦ τ ⟧ps γ') (⟦ ρ ⟧s-cong γ*) (⟦ σ ⟧s-cong γ*)

--Make n explicit in eqTTn-cong₂
data PathSub {Γ} where
  • : PathSub • •
  _,,,_ : ∀ {n Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → Γ ⊢ record { 
    obj = λ γ → eqTTn {_} (⟦ s ⟧⊢ γ) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (⟦ t ⟧⊢ γ) ;
    obj-cong = λ {γ} {γ'} γ* → eqTTn-cong n (⟦ s ⟧⊢-cong γ*) (Typeover.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (⟦ t ⟧⊢-cong γ*) ;
    obj-cong₂ = λ γ* → eqTTn-cong₂ n (⟦ s ⟧⊢-cong₂ γ*) (Typeover.obj-cong₃ T (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ ρ ⟧s-cong₂ γ*) (⟦ σ ⟧s-cong₂ γ*)) (⟦ t ⟧⊢-cong₂ γ*) ;
    obj-cong₃ = λ _ _ _ _ _ _ → trivial n} →
       PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t)

⟦ • ⟧ps γ = ⊤.tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , ⟦ b* ⟧⊢ γ

⟦ • ⟧ps-cong γ* = ⊤.tt
⟦ τ ,,, b* ⟧ps-cong γ* = (⟦ τ ⟧ps-cong γ*) , (⟦ b* ⟧⊢-cong γ*)


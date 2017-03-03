module PathSub2 where
open import Univ
open import Context
open import Syntax
open import PathSub

--Name γ, sq-fill in df of obj
Typeover-eq : ∀ {n Γ Δ} {ρ σ : Sub Γ Δ} {τ : PathSub ρ σ} (T : Typeover n Δ)
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
Typeover-eq {n} {Γ} {Δ} {ρ} {σ} {τ} T F F-cong F-cong₂ G G-cong G-cong₂ = record {
  obj = λ γ → eqTTn (F γ) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (G γ) ;
  obj-cong = λ γ* → eqTTn-cong n (F-cong γ*) (Typeover.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (G-cong γ*) ;
  obj-cong₂ = λ γ₂ → eqTTn-cong₂ n (F-cong₂ γ₂) (Typeover.obj-cong₃ T (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ ρ ⟧s-cong₂ γ₂) (⟦ σ ⟧s-cong₂ γ₂)) (G-cong₂ γ₂) ;
  obj-cong₃ = λ _ _ _ _ _ _ → trivial n }

--Common pattern with df of PathSub?
{- apps : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) →
  Γ ⊢ record {
    obj = λ γ → eqTTn (⟦ x ⟧∋ (⟦ ρ ⟧s γ)) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (⟦ x ⟧∋ (⟦ σ ⟧s γ)) ;
    obj-cong = λ γ* → eqTTn-cong n (⟦ x ⟧∋-cong (⟦ ρ ⟧s-cong γ*)) (Typeover.obj-cong₂ T (⟦ τ ⟧ps-cong γ*)) (⟦ x ⟧∋-cong (⟦ σ ⟧s-cong γ*)) ;
    obj-cong₂ = λ sq-fill → eqTTn-cong₂ {n} (⟦ x ⟧∋-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill)) (Typeover.obj-cong₃ T (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ τ ⟧ps-cong _) (⟦ ρ ⟧s-cong₂ sq-fill) (⟦ σ ⟧s-cong₂ sq-fill)) (⟦ x ⟧∋-cong₂ (⟦ σ ⟧s-cong₂ sq-fill)) ;
    obj-cong₃ = λ _ _ _ _ _ _ → trivial n }
apps (τ ,,, t) top = t
apps (τ ,,, t) (pop x) = apps τ x -}

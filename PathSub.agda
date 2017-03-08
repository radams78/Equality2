module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax
open import Substitution

data  PathSub : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
⟦_⟧ps : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)
⟦_⟧ps-cong : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) {γ γ'} (γ* : EQC Γ γ γ') →
                     EQC₂ {Δ} (mk-square (⟦ τ ⟧ps γ) (⟦ τ ⟧ps γ') (⟦ ρ ⟧s-cong γ*) (⟦ σ ⟧s-cong γ*))
--Given sections s of T[ρ] and t of T[σ], construct the type of all paths s = t over τ
TypeoverFF : ∀ n {Γ Δ} (ρ σ : Sub Γ Δ) (T : Typeover n Δ)
                     (s : ∀ γ → ⟦ T ⟧T (⟦ ρ ⟧s γ))
                     (scong : ∀ {γ} {γ'} (γ* : EQC Γ γ γ') → T ∋ s γ ∼〈 ⟦ ρ ⟧s-cong γ* 〉 s γ')
                     (scong₂ : ∀ {sq} (sq-fill : EQC₂ sq) →
                     [ _ ] scong (Square.North sq) ∼〈〈 eqTTn-cong n (scong (Square.West sq)) (Typeover.obj-cong₂ T _ (⟦ ρ ⟧s-cong₂ sq-fill)) (scong (Square.East sq)) 〉〉 scong (Square.South sq))
                     (τ : PathSub ρ σ)
                     (t : ∀ γ → ⟦ T ⟧T (⟦ σ ⟧s γ))
                     (tcong : ∀ {γ} {γ'} (γ* : EQC Γ γ γ') → T ∋ t γ ∼〈 ⟦ σ ⟧s-cong γ* 〉 t γ')
                     (tcong₂ : ∀ {sq} (sq-fill : EQC₂ sq) →
                     [ _ ] tcong (Square.North sq) ∼〈〈 eqTTn-cong n (tcong (Square.West sq)) (Typeover.obj-cong₂ T _ (⟦ σ ⟧s-cong₂ sq-fill)) (tcong (Square.East sq)) 〉〉 tcong (Square.South sq))
                     → Typeover (pred n) Γ
TypeoverF₂ : ∀ n {Γ Δ} (ρ σ : Sub Γ Δ) (T : Typeover n Δ) →
                     Γ ⊢ TypeoverF ρ T → PathSub ρ σ → Γ ⊢ TypeoverF σ T → Typeover (pred n) Γ

TypeoverFF n ρ σ T s scong scong₂ τ t tcong tcong₂ = record { 
  obj = λ γ → eqTTn {n} (s γ) (Typeover.obj-cong T (⟦ τ ⟧ps γ)) (t γ) ; 
  obj-cong = λ γ* → eqTTn-cong n (scong γ*) (Typeover.obj-cong₂ T _ (⟦ τ ⟧ps-cong γ*)) (tcong γ*) ; 
  obj-cong₂ = λ sq sq-fill → eqTTn-cong₂ {n} (scong₂ sq-fill) (Typeover.obj-cong₃ T _ (⟦ τ ⟧ps-cong (Square.North sq)) (⟦ τ ⟧ps-cong (Square.South sq)) (⟦ τ ⟧ps-cong (Square.West sq)) (⟦ τ ⟧ps-cong (Square.East sq)) (⟦ ρ ⟧s-cong₂ sq-fill) (⟦ σ ⟧s-cong₂ sq-fill)) (tcong₂ sq-fill) ; 
  obj-cong₃ = λ _ _ _ _ _ _ _ → trivial {n} _ _ _ }

TypeoverF₂ n ρ σ T s τ t = TypeoverFF n ρ σ T ⟦ s ⟧⊢ ⟦ s ⟧⊢-cong ⟦ s ⟧⊢-cong₂ τ ⟦ t ⟧⊢ ⟦ t ⟧⊢-cong ⟦ t ⟧⊢-cong₂

data PathSub where
  • : ∀ {Γ} → PathSub {Γ} • •
  _,,,_ : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → Γ ⊢ TypeoverF₂ n ρ σ T s τ t →
       PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t)

⟦ • ⟧ps γ = ⊤.tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , ⟦ b* ⟧⊢ γ

⟦ • ⟧ps-cong γ* = ⊤.tt
⟦ τ ,,, b* ⟧ps-cong γ* = (⟦ τ ⟧ps-cong γ*) , (⟦ b* ⟧⊢-cong γ*)

apps : ∀ {n Γ Δ} {ρ σ : Sub Γ Δ} {T : Typeover n Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) → Γ ⊢ TypeoverFF n ρ σ T 
  (λ γ → ⟦ x ⟧∋ (⟦ ρ ⟧s γ)) (λ γ* → ⟦ x ⟧∋-cong (⟦ ρ ⟧s-cong γ*)) (λ sq-fill → ⟦ x ⟧∋-cong₂ _ (⟦ ρ ⟧s-cong₂ sq-fill)) τ 
  (λ γ → ⟦ x ⟧∋ (⟦ σ ⟧s γ)) (λ γ* → ⟦ x ⟧∋-cong (⟦ σ ⟧s-cong γ*)) (λ sq-fill → ⟦ x ⟧∋-cong₂ _ (⟦ σ ⟧s-cong₂ sq-fill))
apps (τ ,,, e) top = e
apps (τ ,,, e) (pop x) = apps τ x
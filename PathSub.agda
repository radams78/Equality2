module PathSub where
open import Data.Unit
open import Data.Product
open import Univ
open import Context
open import Syntax
<<<<<<< HEAD
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

=======

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

>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
⟦ • ⟧ps γ = ⊤.tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , ⟦ b* ⟧⊢ γ

⟦ • ⟧ps-cong γ* = ⊤.tt
⟦ τ ,,, b* ⟧ps-cong γ* = (⟦ τ ⟧ps-cong γ*) , (⟦ b* ⟧⊢-cong γ*)
<<<<<<< HEAD

apps : ∀ {n Γ Δ} {ρ σ : Sub Γ Δ} {T : Typeover n Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) → Γ ⊢ TypeoverFF n ρ σ T 
  (λ γ → ⟦ x ⟧∋ (⟦ ρ ⟧s γ)) (λ γ* → ⟦ x ⟧∋-cong (⟦ ρ ⟧s-cong γ*)) (λ sq-fill → ⟦ x ⟧∋-cong₂ _ (⟦ ρ ⟧s-cong₂ sq-fill)) τ 
  (λ γ → ⟦ x ⟧∋ (⟦ σ ⟧s γ)) (λ γ* → ⟦ x ⟧∋-cong (⟦ σ ⟧s-cong γ*)) (λ sq-fill → ⟦ x ⟧∋-cong₂ _ (⟦ σ ⟧s-cong₂ sq-fill))
apps (τ ,,, e) top = e
apps (τ ,,, e) (pop x) = apps τ x
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31

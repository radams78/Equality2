module PathSub2 where
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Univ
open import Context
open import Syntax
<<<<<<< HEAD
<<<<<<< HEAD
open import Substitution
open import PathSub

apps-sound : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} {τ : PathSub ρ σ} {x : Δ ∋ T} {γ} → ⟦ apps τ x ⟧⊢ γ ≡ ⟦ x ⟧∋-cong (⟦ τ ⟧ps γ)
apps-sound {ρ = •} {x = ()}
apps-sound {T = record { obj = _ ; obj-cong = _ ; obj-cong₂ = _ ; obj-cong₃ = _ }} {ρ ,,, s} {σ ,,, t} {τ ,,, p} {top} = refl
apps-sound {T = record { obj = _ ; obj-cong = _ ; obj-cong₂ = _ ; obj-cong₃ = _ }} {ρ ,,, s} {σ ,,, t} {τ ,,, p} {pop x} = apps-sound {ρ = ρ} {σ} {τ} {x}

subps : ∀ n {Γ Δ} (T : Typeover n Δ) (ρ σ : Sub Γ Δ) (τ : PathSub ρ σ) (t : Δ ⊢ T) → 
  Γ ⊢ TypeoverFF n ρ σ T (λ γ → ⟦ t ⟧⊢ (⟦ ρ ⟧s γ)) (λ γ* → ⟦ t ⟧⊢-cong (⟦ ρ ⟧s-cong γ*)) (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ ρ ⟧s-cong₂ sq-fill)) τ 
  (λ γ → ⟦ t ⟧⊢ (⟦ σ ⟧s γ)) (λ γ* → ⟦ t ⟧⊢-cong (⟦ σ ⟧s-cong γ*)) (λ sq-fill → ⟦ t ⟧⊢-cong₂ (⟦ σ ⟧s-cong₂ sq-fill))
subps n T ρ σ τ (VAR x) = apps τ x
subps hone {Δ = Δ} .(K hone Δ sets) ρ σ τ PRP = {!!}
=======
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
open import PathSub

apps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ ⟦τ⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} (τ : PathSub ρ σ ⟦τ⟧) (x : Δ ∋ T) →
  Γ ⊢ Typeover-eq {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ (SectionF ⟦ρ⟧ ⟦ x ⟧V) (SectionF ⟦σ⟧ ⟦ x ⟧V) ∋ SectionF₂ ⟦τ⟧ ⟦ x ⟧V
apps (_ ,,, t*) top = t*
apps (τ ,,, _) (pop x) = apps τ x

<<<<<<< HEAD
subps : ∀ {n Γ Δ} {T : Typeover n Δ} {⟦ρ⟧ ⟦σ⟧ ⟦τ⟧ ⟦t⟧}
  {ρ : Sub Γ Δ ⟦ρ⟧} {σ : Sub Γ Δ ⟦σ⟧} → PathSub ρ σ ⟦τ⟧ → Δ ⊢ T ∋ ⟦t⟧ →
  Γ ⊢ Typeover-eq T ⟦τ⟧ (SectionF ⟦ρ⟧ ⟦t⟧) (SectionF ⟦σ⟧ ⟦t⟧) ∋ SectionF₂ ⟦τ⟧ ⟦t⟧
subps τ (VAR x) = apps τ x
subps τ PRP = REF PRP
subps τ (REF t) = {!!}
=======
apps-cong : ∀ {n Γ Δ} {T : Typeover n Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋ T) γ →
  ⟦ apps τ x ⟧⊢ γ ≡ ⟦ x ⟧∋-cong (⟦ τ ⟧ps γ)
apps-cong (_ ,,, _) top _ = refl
apps-cong (τ ,,, _) (pop x) γ = apps-cong τ x γ
<<<<<<< HEAD
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

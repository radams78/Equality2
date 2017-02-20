module Groupoid where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Univ
open import Context U El (λ A B → El (EqU A B)) (λ a p b → El (EqEl a p b))

data tj (Γ : Cx) : (⟦ Γ ⟧C → U) → Set₁
syntax tj Γ (λ γ → A) = γ ∶ Γ ⊢ A
⟦_⟧⊢ : ∀ {Γ T} → tj Γ T → (γ : ⟦ Γ ⟧C) → El (T γ)

data tj Γ where

  var : ∀ {T} → 
      Γ ∋ T →
    ------------
    γ ∶ Γ ⊢ T γ

  one :
    ------------
    _ ∶ Γ ⊢ Prop

  tt :
    ------------
    _ ∶ Γ ⊢ One

  prop :
    ------------
    _ ∶ Γ ⊢ Sets

  iff : ∀
    (φ : _ ∶ Γ ⊢ Prop) → (ψ : _ ∶ Γ ⊢ Prop) →
   ----------------------------------------
                _ ∶ Γ ⊢ Prop
                
⟦ var x ⟧⊢ = ⟦ x ⟧∋
⟦ one ⟧⊢ _ = ONE
⟦ tt ⟧⊢ _ = TT
⟦ prop ⟧⊢ _ = PROP
⟦ iff φ ψ ⟧⊢ γ = IFF (⟦ φ ⟧⊢ γ) (⟦ ψ ⟧⊢ γ)

--A substitution or context morphism from Γ to Δ
data Sub (Γ : Cx) : Cx → Set₁
⟦_⟧s : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C

data Sub Γ where
  • : Sub Γ ε
  _,,,_ : ∀ {Δ T T*} (σ : Sub Γ Δ) → γ ∶ Γ ⊢ T (⟦ σ ⟧s γ) → Sub Γ (Δ ,, T ,, T*)

⟦ • ⟧s γ = lift tt
⟦ σ ,,, t ⟧s γ = ⟦ σ ⟧s γ , ⟦ t ⟧⊢ γ

ap : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ∋ T → γ ∶ Γ ⊢ T (⟦ σ ⟧s γ)
ap (_ ,,, t) top = t
ap (σ ,,, _) (pop x) = ap σ x

ap-sound : ∀ {Γ Δ T} {σ : Sub Γ Δ} {x : Δ ∋ T} {γ} → ⟦ ap σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (⟦ σ ⟧s γ)
ap-sound {σ = •} {x = ()}
ap-sound {σ = _ ,,, _} {x = top} = refl
ap-sound {σ = _ ,,, _} {pop x} = ap-sound {x = x}

sub : ∀ {Γ Δ T} (σ : Sub Γ Δ) → tj Δ T → γ ∶ Γ ⊢ T (⟦ σ ⟧s γ)
sub σ (var x) = ap σ x
sub σ one = one
sub σ tt = tt
sub σ prop = prop
sub σ (iff φ ψ) = iff (sub σ φ) (sub σ ψ)

sub-sound : ∀ {Γ Δ T} {σ : Sub Γ Δ} {t : tj Δ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (⟦ σ ⟧s γ)
sub-sound {t = var x} = ap-sound {x = x}
sub-sound {t = one} = refl
sub-sound {t = tt} = refl
sub-sound {t = prop} = refl
sub-sound {t = iff φ ψ} = cong₂ IFF (sub-sound {t = φ}) (sub-sound {t = ψ})

data PathSub : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
⟦_⟧ps : ∀ {Γ Δ ρ σ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)

data PathSub where
  • : ∀ {Γ} → PathSub {Γ} • •
  _,,,_ : ∀ {Γ Δ T T*} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → γ ∶ Γ ⊢ EqEl (⟦ s ⟧⊢ γ) (T* (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ) (⟦ τ ⟧ps γ)) (⟦ t ⟧⊢ γ) → PathSub {Δ = Δ ,, T ,, T*} (ρ ,,, s) (σ ,,, t)

⟦ • ⟧ps γ = tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , (⟦ b* ⟧⊢ γ)
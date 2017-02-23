module Groupoid where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Univ
open import Context

K : U → ∀ Γ → Type Γ
K A _ = record { 
  obj = λ _ → A ; 
  wd = λ _ → Ref A }

data _⊢_ (Γ : Cx) : Type Γ → Set₁
⟦_⟧⊢ : ∀ {Γ T} → Γ ⊢ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦⟧⊢-cong : ∀ {Γ T} {t : Γ ⊢ T} {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ t ⟧⊢ γ ∼〈 γ* 〉 ⟦ t ⟧⊢ γ'

data _⊢_ Γ where

  var : ∀ {T} → 
      Γ ∋ T →
    ------------
      Γ ⊢ T

  one :
    ------------
    Γ ⊢ K Prop Γ

  tt :
    ------------
    Γ ⊢ K One Γ

  prop :
    ------------
    Γ ⊢ K Sets Γ

  iff : ∀
    (φ : Γ ⊢ K Prop Γ) → (ψ : Γ ⊢ K Prop Γ) →
   ----------------------------------------
                Γ ⊢ K Prop Γ
                
⟦ var x ⟧⊢ = ⟦ x ⟧∋
⟦ one ⟧⊢ _ = ONE
⟦ tt ⟧⊢ _ = TT
⟦ prop ⟧⊢ _ = PROP
⟦ iff φ ψ ⟧⊢ γ = IFF (⟦ φ ⟧⊢ γ) (⟦ ψ ⟧⊢ γ)

⟦⟧⊢-cong {t = var x} γ* = ⟦⟧∋-cong {x = x} γ*
⟦⟧⊢-cong {t = one} γ* = ref
⟦⟧⊢-cong {t = tt} γ* = ref
⟦⟧⊢-cong {t = prop} γ* = ref
⟦⟧⊢-cong {t = iff t t₁} γ* = IFF-cong (⟦⟧⊢-cong {t = t} γ*) (⟦⟧⊢-cong {t = t₁} γ*)

 --A substitution or context morphism from Γ to Δ
data Sub (Γ : Cx) : Cx → Set₁
⟦_⟧s : ∀ {Γ Δ} → Sub Γ Δ → ⟦ Γ ⟧C → ⟦ Δ ⟧C
⟦⟧s-cong : ∀ {Γ Δ} {σ : Sub Γ Δ} {γ γ' : ⟦ Γ ⟧C} → EQC Γ γ γ' → EQC Δ (⟦ σ ⟧s γ) (⟦ σ ⟧s γ')
TypeF : ∀ {Γ Δ} → Sub Γ Δ → Type Δ → Type Γ

data Sub Γ where
  • : Sub Γ ε
  _,,,_ : ∀ {Δ T} (σ : Sub Γ Δ) → Γ ⊢ TypeF σ T → Sub Γ (Δ ,, T)

TypeF σ T = record { 
  obj = λ γ → Type.obj T (⟦ σ ⟧s γ) ; 
  wd = λ γ* → Type.wd T (⟦⟧s-cong γ*) }

⟦ • ⟧s γ = lift tt
⟦ σ ,,, t ⟧s γ = ⟦ σ ⟧s γ , ⟦ t ⟧⊢ γ

⟦⟧s-cong {σ = •} _ = tt
⟦⟧s-cong {σ = σ ,,, t} γ* = (⟦⟧s-cong γ*) , ⟦⟧⊢-cong {t = t} γ*

ap : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ∋ T → Γ ⊢ TypeF σ T
ap (_ ,,, t) top = t
ap (σ ,,, _) (pop x) = ap σ x

ap-sound : ∀ {Γ Δ T} {σ : Sub Γ Δ} {x : Δ ∋ T} {γ} → ⟦ ap σ x ⟧⊢ γ ≡ ⟦ x ⟧∋ (⟦ σ ⟧s γ)
ap-sound {σ = •} {x = ()}
ap-sound {σ = _ ,,, _} {x = top} = refl
ap-sound {σ = _ ,,, _} {pop x} = ap-sound {x = x}

sub : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ⊢ T → Γ ⊢ TypeF σ T
sub σ (var x) = ap σ x
sub σ one = one
sub σ tt = tt
sub σ prop = prop
sub σ (iff φ ψ) = iff (sub σ φ) (sub σ ψ)

sub-sound : ∀ {Γ Δ T} {σ : Sub Γ Δ} {t : Δ ⊢ T} {γ} → ⟦ sub σ t ⟧⊢ γ ≡ ⟦ t ⟧⊢ (⟦ σ ⟧s γ)
sub-sound {t = var x} = ap-sound {x = x}
sub-sound {t = one} = refl
sub-sound {t = tt} = refl
sub-sound {t = prop} = refl
sub-sound {t = iff φ ψ} = cong₂ IFF (sub-sound {t = φ}) (sub-sound {t = ψ})

data PathSub : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Set₁
⟦_⟧ps : ∀ {Γ Δ ρ σ} → PathSub ρ σ → (γ : ⟦ Γ ⟧C) → EQC Δ (⟦ ρ ⟧s γ) (⟦ σ ⟧s γ)
⟦⟧ps-cong : ∀ {Γ Δ ρ σ} (τ : PathSub ρ σ) {γ γ'} (γ* : EQC Γ γ γ') →
  EQC₂ Δ (⟦ τ ⟧ps γ) (⟦ τ ⟧ps γ') (⟦ ρ ⟧s γ*) (⟦ σ ⟧s γ*)

data PathSub where
  • : ∀ {Γ} → PathSub {Γ} • •
  _,,,_ : ∀ {Γ Δ T} {ρ σ : Sub Γ Δ} {s t} (τ : PathSub ρ σ) → Γ ⊢ record { 
    obj = λ γ → EqEl (⟦ s ⟧⊢ γ) (Type.wd T (⟦ τ ⟧ps γ)) (⟦ t ⟧⊢ γ) ; 
    wd = λ γ* → EqEl-cong (Type.wd T (⟦⟧s-cong γ*)) (Type.wd T (⟦⟧s-cong γ*)) 
      (⟦⟧⊢-cong γ*) {!⟦⟧ps-cong!} (⟦⟧⊢-cong γ*) } →
--EqEl (⟦ s ⟧⊢) (Type.wd T (⟦ ρ ⟧s) (⟦ σ ⟧s) (⟦ τ ⟧ps)) (⟦ t ⟧⊢) → 
       PathSub {Δ = Δ ,, T} (ρ ,,, s) (σ ,,, t)

⟦ • ⟧ps γ = tt
⟦ τ ,,, b* ⟧ps γ = (⟦ τ ⟧ps γ) , (⟦ b* ⟧⊢ γ)

⟦⟧ps-cong = {!!}

{- psap : ∀ {Γ Δ T} {ρ σ : Sub Γ Δ} (t : Δ ⊢ T) (τ : PathSub ρ σ) → Γ ⊢ EqEl (⟦ t ⟧⊢ (⟦ ρ ⟧s )) {!!} (⟦ t ⟧⊢ (⟦ σ ⟧s ))
psap t τ = {!!} -}
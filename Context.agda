{-# OPTIONS --rewriting #-}

module Context where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product
open import Univ.HLevel

postulate _▷_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}

data Cx : Set₁
⟦_⟧C : Cx → Set₁
data Functor (Γ : Cx) (n : hLevel) (F : ⟦ Γ ⟧C → Type n) : Set₁
record Typeover (n : hLevel) (Γ : Cx) : Set₁
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
RefC : ∀ {Γ} (γ : ⟦ Γ ⟧C) → EQC Γ γ γ
RefC-cong : ∀ {Γ} {γ γ' : ⟦ Γ ⟧C} (γ* : EQC Γ γ γ') → EQC₂ (RefC γ) (RefC γ') γ* γ*
_∋_∼⟨_⟩_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set


infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : ∀ {n} (Γ : Cx) → Typeover n Γ → Cx

data Functor Γ n F where
  make-Functor : (∀ {γ γ'} (γ* : EQC Γ γ γ') → Eq (F γ) (F γ')) → Functor Γ n F

ap₂ : ∀ {Γ n F} → Functor Γ n F → ∀ {γ γ'} → EQC Γ γ γ' → Eq (F γ) (F γ')
ap₂ (make-Functor F-cong) = F-cong

postulate ap₂-ref : ∀ {Γ n F} (F-cong : Functor Γ n F) (γ : ⟦ Γ ⟧C) → ap₂ F-cong (RefC γ) ▷ Refn (F γ)
{-# REWRITE ap₂-ref #-}

data Functor₂ Γ n F (F-cong : Functor Γ n F) : Set₁ where
  make-Functor₂ : (∀ {γ₁ γ₁' γ₂ γ₂'} (γ₁* : EQC Γ γ₁ γ₁') (γ₂* : EQC Γ γ₂ γ₂') (γₑ : EQC Γ γ₁ γ₂) (γₑ' : EQC Γ γ₁' γ₂')
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') → [ n ] ap₂ F-cong γ₁* ∼⟪ eqn-cong (ap₂ F-cong γₑ) (ap₂ F-cong γₑ') ⟫ ap₂ F-cong γ₂*) →
    Functor₂ Γ n F F-cong

ap₃ : ∀ {Γ n F F-cong} → Functor₂ Γ n F F-cong → ∀ {γ₁ γ₁' γ₂ γ₂'} (γ₁* : EQC Γ γ₁ γ₁') (γ₂* : EQC Γ γ₂ γ₂') (γₑ : EQC Γ γ₁ γ₂) (γₑ' : EQC Γ γ₁' γ₂')
    (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') → [ n ] ap₂ F-cong γ₁* ∼⟪ eqn-cong (ap₂ F-cong γₑ) (ap₂ F-cong γₑ') ⟫ ap₂ F-cong γ₂*
ap₃ (make-Functor₂ F-cong₂) = F-cong₂

postulate ap₃-ref : ∀ {Γ n F F-cong} (F-cong₂ : Functor₂ Γ n F F-cong) {γ γ'} (γ* : EQC Γ γ γ') →
                    ap₃ F-cong₂ (RefC γ) (RefC γ') γ* γ* (RefC-cong γ*) ▷ Refn-cong {n} (ap₂ F-cong γ*)
{-# REWRITE ap₃-ref #-}

record Typeover n Γ where
  field
    obj : ∀ (γ : ⟦ Γ ⟧C) → Type n
    obj-cong : Functor Γ n obj
    obj-cong₂ : Functor₂ Γ n obj obj-cong
    obj-cong₃ : ∀ {γ₁ γ₁' γ₂ γ₂' δ₁ δ₁' δ₂ δ₂' : ⟦ Γ ⟧C}
      {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} {δ₁* : EQC Γ δ₁ δ₁'} {δ₂* : EQC Γ δ₂ δ₂'} {δₑ : EQC Γ δ₁ δ₂} {δₑ' : EQC Γ δ₁' δ₂'} {e₁ : EQC Γ γ₁ δ₁} {e₁' : EQC Γ γ₁' δ₁'} {e₂ : EQC Γ γ₂ δ₂} {e₂' : EQC Γ γ₂' δ₂'}
      (γsq : EQC₂ γ₁* γ₂* γₑ γₑ') (δsq : EQC₂ δ₁* δ₂* δₑ δₑ') (sq₁ : EQC₂ γ₁* δ₁* e₁ e₁') (sq₂ : EQC₂ γ₂* δ₂* e₂ e₂') (sqₑ : EQC₂ γₑ δₑ e₁ e₂) (sqₑ' : EQC₂ γₑ' δₑ' e₁' e₂') →
      [ pred n ] ap₃ obj-cong₂ _ _ _ _ γsq ∼⟪ eqTTn-cong n (ap₃ obj-cong₂ _ _ _ _ sq₁) (eqn-cong₂ n {A₁* = ap₂ obj-cong γₑ} (ap₃ obj-cong₂ _ _ _ _ sqₑ) (ap₃ obj-cong₂ _ _ _ _ sqₑ')) (ap₃ obj-cong₂ _ _ _ _ sq₂) ⟫ ap₃ obj-cong₂ _ _ _ _ δsq

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ

⟦ A ⟧T γ = TT (Typeover.obj A γ)

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼⟨ γ* ⟩ s'

T ∋ a ∼⟨ γ* ⟩ b = [ _ ] a ∼⟪ ap₂ (Typeover.obj-cong T) γ* ⟫ b

RefC {ε} γ = tt
RefC {Γ ,, T} (γ , t) = RefC γ , refn t

EQC₂ {ε} tt tt tt tt = ⊤
EQC₂ {_,,_ {n} Γ T} {a₁ , s₁} {a₂ , s₂} {b₁ , t₁} {b₂ , t₂} (a* , s*) (b* , t*) (e₁ , p₁) (e₂ , p₂) = 
  Σ[ sq ∈ EQC₂ {Γ} a* b* e₁ e₂ ] ([ _ ] s* ∼⟪ eqTTn-cong n p₁ (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) p₂ ⟫ t*)

RefC-cong {ε} _ = tt
RefC-cong {_,,_ {n} Γ T} (γ* , t*) = RefC-cong γ* , refn-cong {n} t*

weak : ∀ {Γ m n} {T : Typeover m Γ} → Typeover n Γ → Typeover n (Γ ,, T)
weak {T = T} S = record { 
  obj = λ {(γ , _) → Typeover.obj S γ};
  obj-cong = make-Functor λ {(γ* , _) → ap₂ (Typeover.obj-cong S) γ*};
  obj-cong₂ = make-Functor₂ λ {_ _ _ _ (γsq , _) → ap₃ (Typeover.obj-cong₂ S) _ _ _ _ γsq};
  obj-cong₃ = λ {(γsq , _) (δsq , _) (sq₁ , _) (sq₂ , _) (sqₑ , _) (sqₑ' , _) → Typeover.obj-cong₃ S γsq δsq sq₁ sq₂ sqₑ sqₑ'}}

infix 5 _∋_
data _∋_ : ∀ {n} (Γ : Cx) (T : Typeover n Γ) → Set₁ where
  top : ∀ {n Γ} {T : Typeover n Γ} → Γ ,, T  ∋ weak T
  pop : ∀ {m n Γ} {S : Typeover m Γ} {T : Typeover n Γ} → Γ ∋ T → Γ ,, S ∋ weak T

⟦_⟧∋ : ∀ {n Γ} {T : Typeover n Γ} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦_⟧∋-cong : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼⟨ γ* ⟩ ⟦ x ⟧∋ γ'
⟦ top ⟧∋-cong (_ , t*) = t*
⟦ pop x ⟧∋-cong (γ* , _) = ⟦ x ⟧∋-cong γ*

⟦_⟧∋-cong₂ : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} 
  {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ _ ] ⟦ x ⟧∋-cong a* ∼⟪ eqTTn-cong n (⟦ x ⟧∋-cong p₁) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) (⟦ x ⟧∋-cong p₂) ⟫ ⟦ x ⟧∋-cong b*
⟦ top ⟧∋-cong₂ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ (γ₂ , _) = ⟦ x ⟧∋-cong₂ γ₂

K : ∀ n Γ → Type n → Typeover n Γ
K n _ A = record { 
  obj = λ _ → A ; 
  obj-cong = make-Functor (λ _ → Refn A) ;
  obj-cong₂ = make-Functor₂ (λ _ _ _ _ _ → Refn-cong (Refn A)) ;
  obj-cong₃ = λ _ _ _ _ _ _ → Refn-cong₂ {n} (Refn-cong (Refn A))}


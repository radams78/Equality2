module Context where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product
open import Univ

data Cx : Set₁
⟦_⟧C : Cx → Set₁
record Type (Γ : Cx) : Set₁
⟦_⟧T : ∀ {Γ} → Type Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
_∋_∼〈_〉_ : ∀ {Γ} T {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : (Γ : Cx) → Type Γ → Cx

record Type Γ where
  field
    obj : ⟦ Γ ⟧C → U
    wd  : ∀ {γ γ'} → EQC Γ γ γ' → obj γ ≃ obj γ'
    wd₂ : ∀ {a₁ a₂ b₁ b₂} (a* : EQC Γ a₁ a₂) (b* : EQC Γ b₁ b₂) (p₁ : EQC Γ a₁ b₁) (p₂ : EQC Γ a₂ b₂) →
      wd a* ∼〈〈 EqU-cong (wd p₁) (wd p₂) 〉〉 wd b*

⟦ T ⟧T γ = El (Type.obj T γ)

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ

T ∋ s ∼〈 γ* 〉 t = El (EqEl s (Type.wd T γ*) t)

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉 s'

EQC₂ {ε} tt tt tt tt = ⊤
EQC₂ {Γ ,, S} {a₁ , s₁} {a₂ , s₂} {b₁ , t₁} {b₂ , t₂} (a* , s*) (b* , t*) (e₁ , p₁) (e₂ , p₂) = 
  Σ[ sq ∈ EQC₂ a* b* e₁ e₂ ] El (EqEl s* (EqEl-cong (Type.wd S e₁) (Type.wd S e₂) p₁ (Type.wd₂ S a* b* e₁ e₂) p₂) t*)

weak-obj : ∀ {Γ} T → Type Γ → ⟦ Γ ,, T ⟧C → U
weak-obj _ S (γ , _) = Type.obj S γ

weak-wd : ∀ {Γ} T (S : Type Γ) (γ γ' : ⟦ Γ ,, T ⟧C) → EQC (Γ ,, T) γ γ' → weak-obj T S γ ≃ weak-obj T S γ'
weak-wd _ S (γ , _) (γ' , _) (γ* , _) = Type.wd S γ*

weak-wd₂ : ∀ {Γ} T (S : Type Γ) {a₁ a₂ b₁ b₂} a* b* p₁ p₂ → 
  weak-wd T S a₁ a₂ a*
    ∼〈〈 EqU-cong (weak-wd T S a₁ b₁ p₁) (weak-wd T S a₂ b₂ p₂) 〉〉
    weak-wd T S b₁ b₂ b*
weak-wd₂ T S (a* , _) (b* , _) (p₁ , _) (p₂ , _) = Type.wd₂ S a* b* p₁ p₂

weak : ∀ {Γ T} → Type Γ → Type (Γ ,, T)
weak {T = T} S = record { 
  obj = weak-obj T S;
  wd = weak-wd T S _ _;
  wd₂ = weak-wd₂ T S}

infix 5 _∋_
data _∋_ : (Γ : Cx) (T : Type Γ) → Set₁ where
  top : ∀ {Γ T} → Γ ,, T  ∋ weak T
  pop : ∀ {Γ S T} → Γ ∋ T → Γ ,, S ∋ weak T

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦⟧∋-cong : ∀ {Γ T} {x : Γ ∋ T} {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼〈 γ* 〉 ⟦ x ⟧∋ γ'
⟦⟧∋-cong {x = top} (_ , t*) = t*
⟦⟧∋-cong {x = pop x} (γ* , _) = ⟦⟧∋-cong {x = x} γ*
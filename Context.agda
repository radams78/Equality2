module Context where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product
open import Univ

data Cx : Set₁
⟦_⟧C : Cx → Set₁
record Type (Γ : Cx) : Set₁
record Setover (Γ : Cx) : Set₁
record Propover (Γ : Cx) : Set₁
⟦_⟧T : ∀ {Γ} → Type Γ → ⟦ Γ ⟧C → Set
⟦_⟧T₀ : ∀ {Γ} → Setover Γ → ⟦ Γ ⟧C → Set
⟦_⟧T₋₁ : ∀ {Γ} → Propover Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
_∋_∼〈_〉_ : ∀ {Γ} T {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set
_∋_∼〈_〉₀_ : ∀ {Γ} S {γ γ'} → ⟦ S ⟧T₀ γ → EQC Γ γ γ' → ⟦ S ⟧T₀ γ' → Set

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : (Γ : Cx) → Type Γ → Cx
  _,,₀_ : ∀ Γ → Setover Γ → Cx
  _,,₋₁_ : ∀ Γ → Propover Γ → Cx

record Type Γ where
  field
    obj : ⟦ Γ ⟧C → U
    obj-cong  : ∀ {γ γ'} → EQC Γ γ γ' → obj γ ⇔ obj γ'
    obj-cong₂ : ∀ {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂} →
      EQC₂ a* b* p₁ p₂ →
      obj-cong a* ∼〈〈 eqU-cong (obj-cong p₁) (obj-cong p₂) 〉〉 obj-cong b*

⟦ T ⟧T γ = Obj (Type.obj T γ)

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ
⟦ Γ ,,₀ S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T₀ γ
⟦ Γ ,,₋₁ φ ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ φ ⟧T₋₁ γ

T ∋ s ∼〈 γ* 〉 t = s ∼〈〈 Type.obj-cong T γ* 〉〉 t

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉 s'
EQC (Γ ,,₀ S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉₀ s'
EQC (Γ ,,₋₁ _) (γ , _) (γ' , _) = EQC Γ γ γ'

EQC₂ {ε} tt tt tt tt = ⊤
EQC₂ {Γ ,, S} {a₁ , s₁} {a₂ , s₂} {b₁ , t₁} {b₂ , t₂} (a* , s*) (b* , t*) (e₁ , p₁) (e₂ , p₂) = 
  Σ[ sq ∈ EQC₂ {Γ} a* b* e₁ e₂ ] s* ∼〈〈 path-cong p₁ (Type.obj-cong₂ S sq) p₂ 〉〉₀ t*
EQC₂ {Γ ,,₀ _} (a* , _) (b* , _) (e₁ , *) (e₂ , _) = EQC₂ {Γ} a* b* e₁ e₂
EQC₂ {Γ ,,₋₁ φ} = EQC₂ {Γ}

record Setover Γ where
  field
    obj : ⟦ Γ ⟧C → Sets
    obj-cong : ∀ {γ} {γ'} → EQC Γ γ γ' → obj γ ≃ obj γ'

record Propover Γ where
  field
    obj : ⟦ Γ ⟧C → Prp

⟦ S ⟧T₀ γ = El (Setover.obj S γ)

⟦ φ ⟧T₋₁ γ = Prf (Propover.obj φ γ)

S ∋ s ∼〈 γ* 〉₀ t = s ∼〈〈 Setover.obj-cong S γ* 〉〉₀ t

weak-obj : ∀ {Γ} T → Type Γ → ⟦ Γ ,, T ⟧C → U
weak-obj _ S (γ , _) = Type.obj S γ

weak-obj-cong : ∀ {Γ} T (S : Type Γ) {γ γ' : ⟦ Γ ,, T ⟧C} → EQC (Γ ,, T) γ γ' → weak-obj T S γ ⇔ weak-obj T S γ'
weak-obj-cong _ S (γ* , _) = Type.obj-cong S γ*

weak-wd₂ : ∀ {Γ} T (S : Type Γ) {a₁ a₂ b₁ b₂} {a* : EQC (Γ ,, T) a₁ a₂} {b* p₁ p₂} → 
  EQC₂ {Γ ,, T} a* b* p₁ p₂ →
  weak-obj-cong T S {a₁} {a₂} a*
    ∼〈〈 eqU-cong (weak-obj-cong T S p₁) (weak-obj-cong T S p₂) 〉〉
    weak-obj-cong T S {b₁} {b₂} b*
weak-wd₂ T S (γ₂ , _) = Type.obj-cong₂ S γ₂

weak : ∀ {Γ T} → Type Γ → Type (Γ ,, T)
weak {T = T} S = record { 
  obj = weak-obj T S;
  obj-cong = weak-obj-cong T S;
  obj-cong₂ = weak-wd₂ T S}

infix 5 _∋_
data _∋_ : (Γ : Cx) (T : Type Γ) → Set₁ where
  top : ∀ {Γ T} → Γ ,, T  ∋ weak T
  pop : ∀ {Γ S T} → Γ ∋ T → Γ ,, S ∋ weak T
--TODO Variables in sets and props

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦_⟧∋-cong : ∀ {Γ T} (x : Γ ∋ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼〈 γ* 〉 ⟦ x ⟧∋ γ'
⟦ top ⟧∋-cong (_ , t*) = t*
⟦ pop x ⟧∋-cong (γ* , _) = ⟦ x ⟧∋-cong γ*

⟦_⟧∋-cong₂ : ∀ {Γ T} (x : Γ ∋ T) {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} 
  {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  ⟦ x ⟧∋-cong a* ∼〈〈 path-cong (⟦ x ⟧∋-cong p₁) (Type.obj-cong₂ T sq) (⟦ x ⟧∋-cong p₂) 〉〉₀ ⟦ x ⟧∋-cong b*
⟦ top ⟧∋-cong₂ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ (γ₂ , _) = ⟦ x ⟧∋-cong₂ γ₂
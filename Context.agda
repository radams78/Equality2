module Context where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product
open import Univ

data hLevel : Set where
  hone : hLevel
  hzero : hLevel
  hminusone : hLevel
  hminustwo : hLevel

pred : hLevel → hLevel
pred hone = hzero
pred hzero = hminusone
pred hminusone = hminustwo
pred hminustwo = hminustwo

Type : hLevel → Set
Type hone = U
Type hzero = Sets
Type hminusone = Prp
Type hminustwo = ⊤

TT : ∀ {n} → Type n → Set
TT {hone} = Obj
TT {hzero} = El
TT {hminusone} = Prf
TT {hminustwo} _ = ⊤

eqn : ∀ {n} → Type n → Type n → Type n
eqn {hone} G H = eqU G H
eqn {hzero} A B = iso A B
eqn {hminusone} φ ψ = iff φ ψ
eqn {hminustwo} _ _ = ⊤.tt

Eq : ∀ {n} → Type n → Type n → Set
Eq A B = TT (eqn A B)

eqTTn : ∀ {n} {A B : Type n} → TT A → Eq A B → TT B → Type (pred n)
eqTTn {hone} = path
eqTTn {hzero} = eq
eqTTn {hminusone} _ _ _ = ⊤.tt
eqTTn {hminustwo} _ _ _ = ⊤.tt

[_]_∼〈〈_〉〉_ : ∀ n {A B : Type n} → TT A → Eq A B → TT B → Set
[ n ] a ∼〈〈 e 〉〉 b = TT (eqTTn a e b)

eqn-cong : ∀ {n} {A₁ A₂ B₁ B₂ : Type n} → Eq A₁ A₂ → Eq B₁ B₂ → Eq (eqn A₁ B₁) (eqn A₂ B₂)
eqn-cong {hone} = eqU-cong
eqn-cong {hzero} = iso-cong
eqn-cong {hminusone} = iff-cong
eqn-cong {hminustwo} _ _ = ⊤.tt

eqTTn-cong : {n : hLevel} 
  {A A' B B' : Type n}
  {e : Eq A B} {e' : Eq A' B'} {A* : Eq A A'} {B* : Eq B B'}
  {a : TT A} {a' : TT A'} {b : TT B} {b' : TT B'} → 
  [ n ] a ∼〈〈 A* 〉〉 a' → [ n ] e ∼〈〈 eqn-cong A* B* 〉〉 e' → [ n ] b ∼〈〈 B* 〉〉 b' →
  Eq (eqTTn a e b) (eqTTn a' e' b')
eqTTn-cong {hone} = path-cong
eqTTn-cong {hzero} = eq-cong
eqTTn-cong {hminusone} _ _ _ = ⊤.tt
eqTTn-cong {hminustwo} _ _ _ = ⊤.tt

eqn-cong₂ : ∀ {n : hLevel}
  {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' : Type n}
  {A₁* : Eq A₁ A₁'} {A₂* : Eq A₂ A₂'} {B₁* : Eq B₁ B₁'} {B₂* : Eq B₂ B₂'} {Aₑ : Eq A₁ A₂} {Aₑ' : Eq A₁' A₂'} {Bₑ : Eq B₁ B₂} {Bₑ' : Eq B₁' B₂'} →
  [ n ] A₁* ∼〈〈 eqn-cong Aₑ Aₑ' 〉〉 A₂* → [ n ] B₁* ∼〈〈 eqn-cong Bₑ Bₑ' 〉〉 B₂* →
  [ n ] eqn-cong A₁* B₁* ∼〈〈 eqn-cong (eqn-cong Aₑ Bₑ) (eqn-cong Aₑ' Bₑ') 〉〉 eqn-cong A₂* B₂*
eqn-cong₂ {hone} = eqU-cong₂
eqn-cong₂ {hzero} = iso-cong₂
eqn-cong₂ {hminusone} _ _ = ⊤.tt
eqn-cong₂ {hminustwo} _ _ = ⊤.tt

data Cx : Set₁
⟦_⟧C : Cx → Set₁
record Typeover (n : hLevel) (Γ : Cx) : Set₁
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
_∋_∼〈_〉n_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : ∀ {n} (Γ : Cx) → Typeover n Γ → Cx

record Typeover n Γ where
  field
    obj : ⟦ Γ ⟧C → Type n
    obj-cong : ∀ {γ γ'} → EQC Γ γ γ' → Eq (obj γ) (obj γ')
    obj-cong₂ : ∀ {γ₁ γ₂ δ₁ δ₂} {γ* : EQC Γ γ₁ γ₂} {δ* : EQC Γ δ₁ δ₂} {e₁ : EQC Γ γ₁ δ₁} {e₂ : EQC Γ γ₂ δ₂} →
      EQC₂ γ* δ* e₁ e₂ → [ n ] obj-cong γ* ∼〈〈 eqn-cong (obj-cong e₁) (obj-cong e₂) 〉〉 obj-cong δ*
    obj-cong₃ : ∀ {γ₁ γ₁' γ₂ γ₂' δ₁ δ₁' δ₂ δ₂' : ⟦ Γ ⟧C}
      {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} {δ₁* : EQC Γ δ₁ δ₁'} {δ₂* : EQC Γ δ₂ δ₂'} {δₑ : EQC Γ δ₁ δ₂} {δₑ' : EQC Γ δ₁' δ₂'} {e₁ : EQC Γ γ₁ δ₁} {e₁' : EQC Γ γ₁' δ₁'} {e₂ : EQC Γ γ₂ δ₂} {e₂' : EQC Γ γ₂' δ₂'}
      (γsq : EQC₂ γ₁* γ₂* γₑ γₑ') (δsq : EQC₂ δ₁* δ₂* δₑ δₑ') (sq₁ : EQC₂ γ₁* δ₁* e₁ e₁') (sq₂ : EQC₂ γ₂* δ₂* e₂ e₂') (sqₑ : EQC₂ γₑ δₑ e₁ e₂) (sqₑ' : EQC₂ γₑ' δₑ' e₁' e₂') →
      [ pred n ] obj-cong₂ γsq ∼〈〈 eqTTn-cong {n} (obj-cong₂ sq₁) (eqn-cong₂ {A₁* = obj-cong γₑ} (obj-cong₂ sqₑ) (obj-cong₂ sqₑ')) (obj-cong₂ sq₂) 〉〉 obj-cong₂ δsq

⟦ A ⟧T γ = TT (Typeover.obj A γ)

T ∋ a ∼〈 γ* 〉n b = [ _ ] a ∼〈〈 Typeover.obj-cong T γ* 〉〉 b

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉n s'

EQC₂ {ε} tt tt tt tt = ⊤
EQC₂ {_,,_ {n} Γ T} {a₁ , s₁} {a₂ , s₂} {b₁ , t₁} {b₂ , t₂} (a* , s*) (b* , t*) (e₁ , p₁) (e₂ , p₂) = 
  Σ[ sq ∈ EQC₂ {Γ} a* b* e₁ e₂ ] ([ _ ] s* ∼〈〈 eqTTn-cong {n} p₁ (Typeover.obj-cong₂ T sq) p₂ 〉〉 t*)

Groupoidover : Cx → Set₁
Groupoidover = Typeover hone

Setover : Cx → Set₁
Setover = Typeover hzero

Propover : Cx → Set₁
Propover = Typeover hminusone

weak : ∀ {Γ m n} {T : Typeover m Γ} → Typeover n Γ → Typeover n (Γ ,, T)
weak {T = T} S = record { 
  obj = λ {(γ , _) → Typeover.obj S γ};
  obj-cong = λ {(γ* , _) → Typeover.obj-cong S γ*};
  obj-cong₂ = λ {(γsq , _) → Typeover.obj-cong₂ S γsq};
  obj-cong₃ = λ {(γsq , _) (δsq , _) (sq₁ , _) (sq₂ , _) (sqₑ , _) (sqₑ' , _) → Typeover.obj-cong₃ S γsq δsq sq₁ sq₂ sqₑ sqₑ'}}

infix 5 _∋_
data _∋_ : ∀ {n} (Γ : Cx) (T : Typeover n Γ) → Set₁ where
  top : ∀ {n Γ} {T : Typeover n Γ} → Γ ,, T  ∋ weak T
  pop : ∀ {m n Γ} {S : Typeover m Γ} {T : Typeover n Γ} → Γ ∋ T → Γ ,, S ∋ weak T

⟦_⟧∋ : ∀ {n Γ} {T : Typeover n Γ} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦_⟧∋-cong : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼〈 γ* 〉n ⟦ x ⟧∋ γ'
⟦ top ⟧∋-cong (_ , t*) = t*
⟦ pop x ⟧∋-cong (γ* , _) = ⟦ x ⟧∋-cong γ*

⟦_⟧∋-cong₂ : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} 
  {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ _ ] ⟦ x ⟧∋-cong a* ∼〈〈 eqTTn-cong {n} (⟦ x ⟧∋-cong p₁) (Typeover.obj-cong₂ T sq) (⟦ x ⟧∋-cong p₂) 〉〉 ⟦ x ⟧∋-cong b*
⟦ top ⟧∋-cong₂ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ (γ₂ , _) = ⟦ x ⟧∋-cong₂ γ₂

K : U → ∀ Γ → Groupoidover Γ
K A _ = record { 
  obj = λ _ → A ; 
  obj-cong = λ _ → Ref A ;
  obj-cong₂ = λ _ → Ref-cong (Ref A) ;
  obj-cong₃ = λ _ _ _ _ _ _ → Ref-cong₂ (Ref-cong (Ref A))}


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
Groupoidover : Cx → Set₁
Setover : Cx → Set₁
Propover : Cx → Set₁
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
_∋_∼〈_〉_ : ∀ {Γ} T {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set
_∋_∼〈_〉₀_ : ∀ {Γ} S {γ γ'} → ⟦ S ⟧T γ → EQC Γ γ γ' → ⟦ S ⟧T γ' → Set

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : (Γ : Cx) → Groupoidover Γ → Cx
  _,,₀_ : ∀ Γ → Setover Γ → Cx
  _,,₋₁_ : ∀ Γ → Propover Γ → Cx

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

Groupoidover = Typeover hone

Setover = Typeover hzero

Propover = Typeover hminusone

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ
⟦ Γ ,,₀ S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ
⟦ Γ ,,₋₁ φ ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ φ ⟧T γ

T ∋ s ∼〈 γ* 〉 t = s ∼〈〈 Typeover.obj-cong T γ* 〉〉 t

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉 s'
EQC (Γ ,,₀ S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉₀ s'
EQC (Γ ,,₋₁ _) (γ , _) (γ' , _) = EQC Γ γ γ'

EQC₂ {ε} tt tt tt tt = ⊤
EQC₂ {Γ ,, S} {a₁ , s₁} {a₂ , s₂} {b₁ , t₁} {b₂ , t₂} (a* , s*) (b* , t*) (e₁ , p₁) (e₂ , p₂) = 
  Σ[ sq ∈ EQC₂ {Γ} a* b* e₁ e₂ ] s* ∼〈〈 path-cong p₁ (Typeover.obj-cong₂ S sq) p₂ 〉〉₀ t*
EQC₂ {Γ ,,₀ _} (a* , _) (b* , _) (e₁ , *) (e₂ , _) = EQC₂ {Γ} a* b* e₁ e₂
EQC₂ {Γ ,,₋₁ φ} = EQC₂ {Γ}

S ∋ s ∼〈 γ* 〉₀ t = s ∼〈〈 Typeover.obj-cong S γ* 〉〉₀ t

weak-obj : ∀ {Γ} T → Groupoidover Γ → ⟦ Γ ,, T ⟧C → U
weak-obj _ S (γ , _) = Typeover.obj S γ

weak-obj-cong : ∀ {Γ} T (S : Groupoidover Γ) {γ γ' : ⟦ Γ ,, T ⟧C} → EQC (Γ ,, T) γ γ' → weak-obj T S γ ⇔ weak-obj T S γ'
weak-obj-cong _ S (γ* , _) = Typeover.obj-cong S γ*

weak-wd₂ : ∀ {Γ} T (S : Groupoidover Γ) {a₁ a₂ b₁ b₂} {a* : EQC (Γ ,, T) a₁ a₂} {b* p₁ p₂} → 
  EQC₂ {Γ ,, T} a* b* p₁ p₂ →
  weak-obj-cong T S {a₁} {a₂} a*
    ∼〈〈 eqU-cong (weak-obj-cong T S p₁) (weak-obj-cong T S p₂) 〉〉
    weak-obj-cong T S {b₁} {b₂} b*
weak-wd₂ T S (γ₂ , _) = Typeover.obj-cong₂ S γ₂

weak : ∀ {Γ T} → Groupoidover Γ → Groupoidover (Γ ,, T)
weak {T = T} S = record { 
  obj = weak-obj T S;
  obj-cong = weak-obj-cong T S;
  obj-cong₂ = weak-wd₂ T S;
  obj-cong₃ = λ {(γsq , _) (δsq , _) (sq₁ , _) (sq₂ , _) (sqₑ , _) (sqₑ' , _) → Typeover.obj-cong₃ S γsq δsq sq₁ sq₂ sqₑ sqₑ'}}

weak₀ : ∀ {Γ S} → Groupoidover Γ → Groupoidover (Γ ,,₀ S)
weak₀ {S = S} T = record { 
  obj = λ {(γ , _) → Typeover.obj T γ} ; 
  obj-cong = λ {(γ* , _) → Typeover.obj-cong T γ*} ; 
  obj-cong₂ = Typeover.obj-cong₂ T ;
  obj-cong₃ = Typeover.obj-cong₃ T }

weak₋₁ : ∀ {Γ φ} → Groupoidover Γ → Groupoidover (Γ ,,₋₁ φ)
weak₋₁ {φ = φ} T = record { 
  obj = λ {(γ , _) → Typeover.obj T γ} ; 
  obj-cong = Typeover.obj-cong T ; 
  obj-cong₂ = Typeover.obj-cong₂ T ;
  obj-cong₃ = Typeover.obj-cong₃ T }

infix 5 _∋_
data _∋_ : (Γ : Cx) (T : Groupoidover Γ) → Set₁ where
  top : ∀ {Γ T} → Γ ,, T  ∋ weak T
  pop : ∀ {Γ S T} → Γ ∋ T → Γ ,, S ∋ weak T
  pop₀ : ∀ {Γ S T} → Γ ∋ T → Γ ,,₀ S ∋ weak₀ T
  pop₋₁ : ∀ {Γ φ T} → Γ ∋ T → Γ ,,₋₁ φ ∋ weak₋₁ T

⟦_⟧∋ : ∀ {Γ T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ
⟦ pop₀ i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ
⟦ pop₋₁ i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦_⟧∋-cong : ∀ {Γ T} (x : Γ ∋ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼〈 γ* 〉 ⟦ x ⟧∋ γ'
⟦ top ⟧∋-cong (_ , t*) = t*
⟦ pop x ⟧∋-cong (γ* , _) = ⟦ x ⟧∋-cong γ*
⟦ pop₀ i ⟧∋-cong (γ* , _) = ⟦ i ⟧∋-cong γ*
⟦ pop₋₁ i ⟧∋-cong γ* = ⟦ i ⟧∋-cong γ*

⟦_⟧∋-cong₂ : ∀ {Γ T} (x : Γ ∋ T) {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} 
  {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  ⟦ x ⟧∋-cong a* ∼〈〈 path-cong (⟦ x ⟧∋-cong p₁) (Typeover.obj-cong₂ T sq) (⟦ x ⟧∋-cong p₂) 〉〉₀ ⟦ x ⟧∋-cong b*
⟦ top ⟧∋-cong₂ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ (γ₂ , _) = ⟦ x ⟧∋-cong₂ γ₂
⟦ pop₀ i ⟧∋-cong₂ γ₂ = ⟦ i ⟧∋-cong₂ γ₂
⟦ pop₋₁ i ⟧∋-cong₂ γ₂ = ⟦ i ⟧∋-cong₂ γ₂

--TODO Variables in sets and propositions

K : U → ∀ Γ → Groupoidover Γ
K A _ = record { 
  obj = λ _ → A ; 
  obj-cong = λ _ → Ref A ;
  obj-cong₂ = λ _ → Ref-cong (Ref A) ;
  obj-cong₃ = λ _ _ _ _ _ _ → Ref-cong₂ (Ref-cong (Ref A))}


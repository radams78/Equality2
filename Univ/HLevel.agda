module Univ.HLevel where
open import Data.Unit
open import Univ.Univ
open import Univ.Prp
open import Univ.Sets
open import Univ.Groupoid

--TODO Enforce variable conventions

------------------------------------------------------
-- The structures that exist at every level
------------------------------------------------------

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
eqn {hminustwo} _ _ = tt

Eq : ∀ {n} → Type n → Type n → Set
Eq A B = TT (eqn A B)

eqTTn : ∀ {n} {A B : Type n} → TT A → Eq A B → TT B → Type (pred n)
eqTTn {hone} = path
eqTTn {hzero} = eq
eqTTn {hminusone} _ _ _ = tt
eqTTn {hminustwo} _ _ _ = tt

[_]_∼⟪_⟫_ : ∀ n {A B : Type n} → TT A → Eq A B → TT B → Set
[ n ] a ∼⟪ e ⟫ b = TT (eqTTn a e b)

eqn-cong : ∀ {n} {A₁ A₂ B₁ B₂ : Type n} → Eq A₁ A₂ → Eq B₁ B₂ → Eq (eqn A₁ B₁) (eqn A₂ B₂)
eqn-cong {hone} = eqU-cong
eqn-cong {hzero} = iso-cong
eqn-cong {hminusone} = iff-cong
eqn-cong {hminustwo} _ _ = tt

eqTTn-cong : (n : hLevel) 
  {A A' B B' : Type n}
  {e : Eq A B} {e' : Eq A' B'} {A* : Eq A A'} {B* : Eq B B'}
  {a : TT A} {a' : TT A'} {b : TT B} {b' : TT B'} → 
  [ n ] a ∼⟪ A* ⟫ a' → [ n ] e ∼⟪ eqn-cong A* B* ⟫ e' → [ n ] b ∼⟪ B* ⟫ b' →
  Eq (eqTTn a e b) (eqTTn a' e' b')
eqTTn-cong hone = path-cong
eqTTn-cong hzero = eq-cong
eqTTn-cong hminusone _ _ _ = tt
eqTTn-cong hminustwo _ _ _ = tt

eqn-cong₂ : ∀ (n : hLevel)
  {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' : Type n}
  {A₁* : Eq A₁ A₁'} {A₂* : Eq A₂ A₂'} {B₁* : Eq B₁ B₁'} {B₂* : Eq B₂ B₂'} {Aₑ : Eq A₁ A₂} {Aₑ' : Eq A₁' A₂'} {Bₑ : Eq B₁ B₂} {Bₑ' : Eq B₁' B₂'} →
  [ n ] A₁* ∼⟪ eqn-cong Aₑ Aₑ' ⟫ A₂* → [ n ] B₁* ∼⟪ eqn-cong Bₑ Bₑ' ⟫ B₂* →
  [ n ] eqn-cong A₁* B₁* ∼⟪ eqn-cong (eqn-cong Aₑ Bₑ) (eqn-cong Aₑ' Bₑ') ⟫ eqn-cong A₂* B₂*
eqn-cong₂ hone = eqU-cong₂
eqn-cong₂ hzero = iso-cong₂'
eqn-cong₂ hminusone _ _ = tt
eqn-cong₂ hminustwo _ _ = tt

eqn-cong₃ : ∀ (n : hLevel)
  {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' C₁ C₁' C₂ C₂' D₁ D₁' D₂ D₂' : Type n}
  {A₁* : Eq A₁ A₁'} {A₂* : Eq A₂ A₂'} {B₁* : Eq B₁ B₁'} {B₂* : Eq B₂ B₂'} {C₁* : Eq C₁ C₁'} {C₂* : Eq C₂ C₂'} {D₁* : Eq D₁ D₁'} {D₂* : Eq D₂ D₂'}
  {Aₑ : Eq A₁ A₂} {Aₑ' : Eq A₁' A₂'} {Bₑ : Eq B₁ B₂} {Bₑ' : Eq B₁' B₂'} {Cₑ : Eq C₁ C₂} {Cₑ' : Eq C₁' C₂'} {Dₑ : Eq D₁ D₂} {Dₑ' : Eq D₁' D₂'}
  {F₁ : Eq A₁ C₁} {F₁' : Eq A₁' C₁'} {F₂ : Eq A₂ C₂} {F₂' : Eq A₂' C₂'}
  {G₁ : Eq B₁ D₁} {G₁' : Eq B₁' D₁'} {G₂ : Eq B₂ D₂} {G₂' : Eq B₂' D₂'}
  {Aₑ* : [ n ] A₁* ∼⟪ eqn-cong Aₑ Aₑ' ⟫ A₂*} {Bₑ* : [ n ] B₁* ∼⟪ eqn-cong Bₑ Bₑ' ⟫ B₂*} {Cₑ* : [ n ] C₁* ∼⟪ eqn-cong Cₑ Cₑ' ⟫ C₂*} {Dₑ* : [ n ] D₁* ∼⟪ eqn-cong Dₑ Dₑ' ⟫ D₂*}
  {F₁* : [ n ] A₁* ∼⟪ eqn-cong F₁ F₁' ⟫ C₁*} {Fₑ : [ n ] Aₑ ∼⟪ eqn-cong F₁ F₂ ⟫ Cₑ} {Fₑ' : [ n ] Aₑ' ∼⟪ eqn-cong F₁' F₂' ⟫ Cₑ'} {F₂* : [ n ] A₂* ∼⟪ eqn-cong F₂ F₂' ⟫ C₂*}
  {G₁* : [ n ] B₁* ∼⟪ eqn-cong G₁ G₁' ⟫ D₁*} {Gₑ : [ n ] Bₑ ∼⟪ eqn-cong G₁ G₂ ⟫ Dₑ} {Gₑ' : [ n ] Bₑ' ∼⟪ eqn-cong G₁' G₂' ⟫ Dₑ'} {G₂* : [ n ] B₂* ∼⟪ eqn-cong G₂ G₂' ⟫ D₂*} →
  [ pred n ] Aₑ* ∼⟪ eqTTn-cong n F₁* (eqn-cong₂ n Fₑ Fₑ') F₂* ⟫ Cₑ* → [ pred n ] Bₑ* ∼⟪ eqTTn-cong n G₁* (eqn-cong₂ n Gₑ Gₑ') G₂* ⟫ Dₑ* →
  [ pred n ] eqn-cong₂ n Aₑ* Bₑ* ∼⟪ eqTTn-cong n (eqn-cong₂ n F₁* G₁*) (eqn-cong₂ n (eqn-cong₂ n Fₑ Gₑ) (eqn-cong₂ n Fₑ' Gₑ')) (eqn-cong₂ n F₂* G₂*) ⟫ eqn-cong₂ n Cₑ* Dₑ*
eqn-cong₃ hone = eqU-cong₃ 
eqn-cong₃ hzero _ _ = tt
eqn-cong₃ hminusone _ _ = tt
eqn-cong₃ hminustwo _ _ = tt

eqTTn-cong₂ : ∀ (n : hLevel)
  {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' : Type n}
  {e₁ : Eq A₁ B₁} {e₁' : Eq A₁' B₁'} {e₂ : Eq A₂ B₂} {e₂' : Eq A₂' B₂'} {A₁* : Eq A₁ A₁'} {B₁* : Eq B₁ B₁'} {A₂* : Eq A₂ A₂'} {B₂* : Eq B₂ B₂'} {Aₑ : Eq A₁ A₂} {Aₑ' : Eq A₁' A₂'} {Bₑ : Eq B₁ B₂} {Bₑ' : Eq B₁' B₂'}
  {a₁ : TT A₁} {a₁' : TT A₁'} {a₂ : TT A₂} {a₂' : TT A₂'} {b₁ : TT B₁} {b₁' : TT B₁'} {b₂ : TT B₂} {b₂' : TT B₂'}
  {e₁* : [ n ] e₁ ∼⟪ eqn-cong A₁* B₁* ⟫ e₁'} {e₂* : [ n ] e₂ ∼⟪ eqn-cong A₂* B₂* ⟫ e₂'} {Aₑ* : [ n ] A₁* ∼⟪ eqn-cong Aₑ Aₑ' ⟫ A₂*}
  {eₑ : [ n ] e₁ ∼⟪ eqn-cong Aₑ Bₑ ⟫ e₂} {Bₑ* : [ n ] B₁* ∼⟪ eqn-cong Bₑ Bₑ' ⟫ B₂*} {eₑ' : [ n ] e₁' ∼⟪ eqn-cong Aₑ' Bₑ' ⟫ e₂'}
  {a₁* : [ n ] a₁ ∼⟪ A₁* ⟫ a₁'} {a₂* : [ n ] a₂ ∼⟪ A₂* ⟫ a₂'} {b₁* : [ n ] b₁ ∼⟪ B₁* ⟫ b₁'} {b₂* : [ n ] b₂ ∼⟪ B₂* ⟫ b₂'}
  {aₑ : [ n ] a₁ ∼⟪ Aₑ ⟫ a₂} {aₑ' : [ n ] a₁' ∼⟪ Aₑ' ⟫ a₂'} {bₑ : [ n ] b₁ ∼⟪ Bₑ ⟫ b₂} {bₑ' : [ n ] b₁' ∼⟪ Bₑ' ⟫ b₂'} →
  [ pred n ] a₁* ∼⟪ eqTTn-cong n aₑ Aₑ* aₑ' ⟫ a₂* → [ pred n ] e₁* ∼⟪ eqTTn-cong n eₑ (eqn-cong₂ n Aₑ* Bₑ*) eₑ' ⟫ e₂* → [ pred n ] b₁* ∼⟪ eqTTn-cong n bₑ Bₑ* bₑ' ⟫ b₂* →
  [ pred n ] eqTTn-cong n a₁* e₁* b₁* ∼⟪ eqn-cong (eqTTn-cong n aₑ eₑ bₑ) (eqTTn-cong n aₑ' eₑ' bₑ') ⟫ eqTTn-cong n a₂* e₂* b₂*
eqTTn-cong₂ hone = path-cong₂
eqTTn-cong₂ hzero _ _ _ = tt
eqTTn-cong₂ hminusone _ _ _ = tt
eqTTn-cong₂ hminustwo _ _ _ = tt

Refn : ∀ {n} (A : Type n) → Eq A A
Refn {hone} A = Ref A
Refn {hzero} A = Ref₀ A
Refn {hminusone} A = Ref₋₁ A
Refn {hminustwo} A = tt

Refn-cong : ∀ {n} {A B : Type n} (e : Eq A B) → [ _ ] Refn A ∼⟪ eqn-cong e e ⟫ Refn B
Refn-cong {hone} e = Ref-cong e
Refn-cong {hzero} e = Ref₀-cong e
Refn-cong {hminusone} e = tt
Refn-cong {hminustwo} e = tt

Refn-cong₂ : ∀ {n : hLevel}
  {A A' B B' : Type n}
  {e : Eq A B} {e' : Eq A' B'} {A* : Eq A A'} {B* : Eq B B'}
  (sq : [ _ ] e ∼⟪ eqn-cong A* B* ⟫ e') →
  [ _ ] Refn-cong e ∼⟪ eqTTn-cong n (Refn-cong A*) (eqn-cong₂ n sq sq) (Refn-cong B*) ⟫ Refn-cong e'
Refn-cong₂ {hone} = Ref-cong₂
Refn-cong₂ {hzero} _ = tt
Refn-cong₂ {hminusone} _ = tt
Refn-cong₂ {hminustwo} _ = tt

refn : ∀ {n : hLevel} {A : Type n} (a : TT A) → [ n ] a ∼⟪ Refn A ⟫ a
refn {hone} a = ref a
refn {hzero} _ = ref₀
refn {hminusone} _ = tt
refn {hminustwo} _ = tt

refn-cong : ∀ {n : hLevel}
  {A A' : Type n}
  {A* : Eq A A'}
  {a : TT A} {a' : TT A'}
  (a* : [ n ] a ∼⟪ A* ⟫ a') →
  [ pred n ] refn a ∼⟪ eqTTn-cong n a* (Refn-cong A*) a* ⟫ refn a'
refn-cong {hone} a* = ref-cong a*
refn-cong {hzero} _ = tt
refn-cong {hminusone} _ = tt
refn-cong {hminustwo} _ = tt

trivial : ∀ n {A B : Type (pred (pred n))} {a : TT A} {e : Eq A B} {b : TT B} → [ pred (pred n) ] a ∼⟪ e ⟫ b
trivial hone = tt
trivial hzero = tt
trivial hminusone = tt
trivial hminustwo = tt

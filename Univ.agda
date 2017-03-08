module Univ where
open import Data.Unit

--TODO Divide into separate modules for props, sets, groupoids

postulate U : Set
postulate Obj : U → Set

postulate sets : U
Sets : Set
Sets = Obj sets

postulate El : Sets → Set

postulate prp : Sets
Prp : Set
Prp = El prp

postulate Prf : Prp → Set

postulate one : Prp
One : Set
One = Prf one

-- The Unit

postulate star : One

-- Propositions

postulate iff : Prp → Prp → Prp
_↔_ : Prp → Prp → Set
φ ↔ ψ = Prf (iff φ ψ)

postulate iff-cong : ∀ {φ φ' ψ ψ'} → φ ↔ φ' → ψ ↔ ψ' → iff φ ψ ↔ iff φ' ψ'

postulate Ref₋₁ : ∀ φ → φ ↔ φ

-- Sets

postulate iso : Sets → Sets → Sets
_≃_ : Sets → Sets → Set
A ≃ B = El (iso A B)

postulate iso-cong : ∀ {A A' B B'} → A ≃ A' → B ≃ B' → iso A B ≃ iso A' B'

postulate eq : ∀ {A B} → El A → A ≃ B → El B → Prp
private _∼⟪_⟫₀_ : ∀ {A B} → El A → A ≃ B → El B → Set
a ∼⟪ e ⟫₀ b = Prf (eq a e b)

--TODO Extract Square type
postulate iso-cong₂ : ∀ {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂'}
                    {A₁* : A₁ ≃ A₁'} {B₁* : B₁ ≃ B₁'} {A₂* : A₂ ≃ A₂'} {B₂* : B₂ ≃ B₂'}
                    {Aₑ : A₁ ≃ A₂} {Aₑ' : A₁' ≃ A₂'} {Bₑ : B₁ ≃ B₂} {Bₑ' : B₁' ≃ B₂'} →
                    A₁* ∼⟪ iso-cong Aₑ Aₑ' ⟫₀ A₂* → B₁* ∼⟪ iso-cong Bₑ Bₑ' ⟫₀ B₂* →
                    iso-cong A₁* B₁* ∼⟪ iso-cong (iso-cong Aₑ Bₑ) (iso-cong Aₑ' Bₑ') ⟫₀ iso-cong A₂* B₂*

postulate eq-cong : ∀ {A A' B B' a a' f f' b b'} {A* : A ≃ A'} {B* : B ≃ B'} → 
                  a ∼⟪ A* ⟫₀ a' → f ∼⟪ iso-cong A* B* ⟫₀ f' → b ∼⟪ B* ⟫₀ b' → 
                  eq a f b ↔ eq a' f' b'

postulate Ref₀ : ∀ A → A ≃ A

postulate Ref₀-cong : ∀ {A} {B} (e : A ≃ B) → Ref₀ A ∼⟪ iso-cong e e ⟫₀ Ref₀ B

postulate ref₀ : ∀ {A} {a} → a ∼⟪ Ref₀ A ⟫₀ a

-- Groupoids

postulate eqU : U → U → U
_⇔_ : U → U → Set
A ⇔ B = Obj (eqU A B)

postulate eqU-cong : ∀ {A A' B B'} → A ⇔ B → A' ⇔ B' → eqU A A' ⇔ eqU B B'

postulate path : ∀ {A B} → Obj A → A ⇔ B → Obj B → Sets
private _∼⟪_⟫_ : ∀ {A B} → Obj A → A ⇔ B → Obj B → Set
a ∼⟪ φ ⟫ b = El (path a φ b)

postulate eqU-cong₂ : ∀ {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂'}
                    {A₁* : A₁ ⇔ A₁'} {B₁* : B₁ ⇔ B₁'} {A₂* B₂*}
                    {A* : A₁ ⇔ A₂} {A'* : A₁' ⇔ A₂'} {B* : B₁ ⇔ B₂} {B'* : B₁' ⇔ B₂'} → 
                    A₁* ∼⟪ eqU-cong A* A'* ⟫ A₂* → B₁* ∼⟪ eqU-cong B* B'* ⟫ B₂* → 
                    eqU-cong A₁* B₁* ∼⟪ eqU-cong (eqU-cong A* B*) (eqU-cong A'* B'*) ⟫ eqU-cong A₂* B₂*

postulate path-cong : ∀ {A A' B B' a a' b b' φ φ'} {A* : A ⇔ A'} {B* : B ⇔ B'} → 
                    a ∼⟪ A* ⟫ a' → φ ∼⟪ eqU-cong A* B* ⟫ φ' → b ∼⟪ B* ⟫ b' → 
                    path a φ b ≃ path a' φ' b'

--TODO Extract cube type
postulate eqU-cong₃ : ∀ {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' C₁ C₁' C₂ C₂' D₁ D₁' D₂ D₂' : U} 
                      {A₁* : A₁ ⇔ A₁'} {A₂* : A₂ ⇔ A₂'} {Aₑ : A₁ ⇔ A₂} {Aₑ' : A₁' ⇔ A₂'} 
                      {B₁* : B₁ ⇔ B₁'} {B₂* : B₂ ⇔ B₂'} {Bₑ : B₁ ⇔ B₂} {Bₑ' : B₁' ⇔ B₂'} 
                      {C₁* : C₁ ⇔ C₁'} {C₂* : C₂ ⇔ C₂'} {Cₑ : C₁ ⇔ C₂} {Cₑ' : C₁' ⇔ C₂'} 
                      {D₁* : D₁ ⇔ D₁'} {D₂* : D₂ ⇔ D₂'} {Dₑ : D₁ ⇔ D₂} {Dₑ' : D₁' ⇔ D₂'} 
                      {F₁ : A₁ ⇔ B₁} {F₁' : A₁' ⇔ B₁'} {F₂ : A₂ ⇔ B₂} {F₂' : A₂' ⇔ B₂'}
                      {G₁ : C₁ ⇔ D₁} {G₁' : C₁' ⇔ D₁'} {G₂ : C₂ ⇔ D₂} {G₂' : C₂' ⇔ D₂'}
                      {H₁ : A₁ ⇔ C₁} {H₁' : A₁' ⇔ C₁'} {H₂ : A₂ ⇔ C₂} {H₂' : A₂' ⇔ C₂'}
                      {K₁ : B₁ ⇔ D₁} {K₁' : B₁' ⇔ D₁'} {K₂ : B₂ ⇔ D₂} {K₂' : B₂' ⇔ D₂'}
                      {Aₑ* : A₁* ∼⟪ eqU-cong Aₑ Aₑ' ⟫ A₂*}
                      {Bₑ* : B₁* ∼⟪ eqU-cong Bₑ Bₑ' ⟫ B₂*}
                      {Cₑ* : C₁* ∼⟪ eqU-cong Cₑ Cₑ' ⟫ C₂*}
                      {Dₑ* : D₁* ∼⟪ eqU-cong Dₑ Dₑ' ⟫ D₂*}
                      {H₁* : A₁* ∼⟪ eqU-cong H₁ H₁' ⟫ C₁*}
                      {H₂* : A₂* ∼⟪ eqU-cong H₂ H₂' ⟫ C₂*}
                      {Hₑ : Aₑ ∼⟪ eqU-cong H₁ H₂ ⟫ Cₑ}
                      {Hₑ' : Aₑ' ∼⟪ eqU-cong H₁' H₂' ⟫ Cₑ'}
                      {K₁* : B₁* ∼⟪ eqU-cong K₁ K₁' ⟫ D₁*}
                      {K₂* : B₂* ∼⟪ eqU-cong K₂ K₂' ⟫ D₂*}
                      {Kₑ : Bₑ ∼⟪ eqU-cong K₁ K₂ ⟫ Dₑ}
                      {Kₑ' : Bₑ' ∼⟪ eqU-cong K₁' K₂' ⟫ Dₑ'} → 
                      Aₑ* ∼⟪ path-cong H₁* (eqU-cong₂ Hₑ Hₑ') H₂* ⟫₀ Cₑ* → 
                      Bₑ* ∼⟪ path-cong K₁* (eqU-cong₂ Kₑ Kₑ') K₂* ⟫₀ Dₑ* → 
                      eqU-cong₂ Aₑ* Bₑ* ∼⟪ path-cong (eqU-cong₂ H₁* K₁*) (eqU-cong₂ (eqU-cong₂ Hₑ Kₑ) (eqU-cong₂ Hₑ' Kₑ')) (eqU-cong₂ H₂* K₂*) ⟫₀ eqU-cong₂ Cₑ* Dₑ*

postulate path-cong₂ : ∀ {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' : U}
                         {A₁* : A₁ ⇔ A₁'} {A₂* : A₂ ⇔ A₂'} {B₁* : B₁ ⇔ B₁'} {B₂* : B₂ ⇔ B₂'} {φ₁ : A₁ ⇔ B₁} {φ₁' : A₁' ⇔ B₁'} {φ₂ : A₂ ⇔ B₂} {φ₂' : A₂' ⇔ B₂'} {Aₑ : A₁ ⇔ A₂} {Aₑ' : A₁' ⇔ A₂'} {Bₑ : B₁ ⇔ B₂} {Bₑ' : B₁' ⇔ B₂'}
                         {a₁ : Obj A₁} {a₁' : Obj A₁'} {a₂ : Obj A₂} {a₂' : Obj A₂'} {b₁ : Obj B₁} {b₁' : Obj B₁'} {b₂ : Obj B₂} {b₂' : Obj B₂'}
                         {a₁* : a₁ ∼⟪ A₁* ⟫ a₁'} {a₂* : a₂ ∼⟪ A₂* ⟫ a₂'} {b₁* : b₁ ∼⟪ B₁* ⟫ b₁'} {b₂* : b₂ ∼⟪ B₂* ⟫ b₂'} {aₑ : a₁ ∼⟪ Aₑ ⟫ a₂} {aₑ' : a₁' ∼⟪ Aₑ' ⟫ a₂'} {φₑ : φ₁ ∼⟪ eqU-cong Aₑ Bₑ ⟫ φ₂} {φₑ' : φ₁' ∼⟪ eqU-cong Aₑ' Bₑ' ⟫ φ₂'} {bₑ : b₁ ∼⟪ Bₑ ⟫ b₂} {bₑ' : b₁' ∼⟪ Bₑ' ⟫ b₂'}
                         {φ₁* : φ₁ ∼⟪ eqU-cong A₁* B₁* ⟫ φ₁'} {φ₂* : φ₂ ∼⟪ eqU-cong A₂* B₂* ⟫ φ₂'} {Aₑ* : A₁* ∼⟪ eqU-cong Aₑ Aₑ' ⟫ A₂*} {Bₑ* : B₁* ∼⟪ eqU-cong Bₑ Bₑ' ⟫ B₂*} → 
                         a₁* ∼⟪ path-cong aₑ Aₑ* aₑ' ⟫₀ a₂* → φ₁* ∼⟪ path-cong φₑ (eqU-cong₂ Aₑ* Bₑ*) φₑ' ⟫₀ φ₂* → b₁* ∼⟪ path-cong bₑ Bₑ* bₑ' ⟫₀ b₂* → 
                         path-cong a₁* φ₁* b₁* ∼⟪ iso-cong (path-cong aₑ φₑ bₑ) (path-cong aₑ' φₑ' bₑ') ⟫₀ path-cong a₂* φ₂* b₂*

postulate Ref : ∀ A → A ⇔ A

postulate Ref-cong : ∀ {A B} (F : A ⇔ B) → Ref A ∼⟪ eqU-cong F F ⟫ Ref B

postulate Ref-cong₂ : {!!}

postulate ref : ∀ {A} (a : Obj A) → a ∼⟪ Ref A ⟫ a

postulate ref-cong : {!!}

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

[_]_∼〈〈_〉〉_ : ∀ n {A B : Type n} → TT A → Eq A B → TT B → Set
[ n ] a ∼〈〈 e 〉〉 b = TT (eqTTn a e b)

eqn-cong : ∀ {n} {A₁ A₂ B₁ B₂ : Type n} → Eq A₁ A₂ → Eq B₁ B₂ → Eq (eqn A₁ B₁) (eqn A₂ B₂)
eqn-cong {hone} = eqU-cong
eqn-cong {hzero} = iso-cong
eqn-cong {hminusone} = iff-cong
eqn-cong {hminustwo} _ _ = tt

eqTTn-cong : (n : hLevel)
  {A A' B B' : Type n}
  {e : Eq A B} {e' : Eq A' B'} {A* : Eq A A'} {B* : Eq B B'}
  {a : TT A} {a' : TT A'} {b : TT B} {b' : TT B'} → 
  [ n ] a ∼〈〈 A* 〉〉 a' → [ n ] e ∼〈〈 eqn-cong A* B* 〉〉 e' → [ n ] b ∼〈〈 B* 〉〉 b' →
  Eq (eqTTn a e b) (eqTTn a' e' b')
eqTTn-cong {hone} = path-cong
eqTTn-cong {hzero} = eq-cong
eqTTn-cong {hminusone} _ _ _ = tt
eqTTn-cong {hminustwo} _ _ _ = tt

eqn-cong₂ : ∀ {n : hLevel}
  {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' : Type n}
  {A₁* : Eq A₁ A₁'} {A₂* : Eq A₂ A₂'} {B₁* : Eq B₁ B₁'} {B₂* : Eq B₂ B₂'} {Aₑ : Eq A₁ A₂} {Aₑ' : Eq A₁' A₂'} {Bₑ : Eq B₁ B₂} {Bₑ' : Eq B₁' B₂'} →
  [ n ] A₁* ∼〈〈 eqn-cong Aₑ Aₑ' 〉〉 A₂* → [ n ] B₁* ∼〈〈 eqn-cong Bₑ Bₑ' 〉〉 B₂* →
  [ n ] eqn-cong A₁* B₁* ∼〈〈 eqn-cong (eqn-cong Aₑ Bₑ) (eqn-cong Aₑ' Bₑ') 〉〉 eqn-cong A₂* B₂*
eqn-cong₂ {hone} = eqU-cong₂
eqn-cong₂ {hzero} = iso-cong₂
eqn-cong₂ {hminusone} _ _ = tt
eqn-cong₂ {hminustwo} _ _ = tt

eqTTn-cong₂ : ∀ {n : hLevel}
  {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' : Type n}
  {e₁ : Eq A₁ B₁} {e₁' : Eq A₁' B₁'} {e₂ : Eq A₂ B₂} {e₂' : Eq A₂' B₂'} {A₁* : Eq A₁ A₁'} {A₂* : Eq A₂ A₂'} {B₁* : Eq B₁ B₁'} {B₂* : Eq B₂ B₂'} {Aₑ : Eq A₁ A₂} {Aₑ' : Eq A₁' A₂'} {Bₑ : Eq B₁ B₂} {Bₑ' : Eq B₁' B₂'}
  {a₁ : TT A₁} {a₁' : TT A₁'} {a₂ : TT A₂} {a₂' : TT A₂'} {b₁ : TT B₁} {b₁' : TT B₁'} {b₂ : TT B₂} {b₂' : TT B₂'}
  {a₁* : [ n ] a₁ ∼〈〈 A₁* 〉〉 a₁'} {a₂* : [ n ] a₂ ∼〈〈 A₂* 〉〉 a₂'} {b₁* : [ n ] b₁ ∼〈〈 B₁* 〉〉 b₁'} {b₂* : [ n ] b₂ ∼〈〈 B₂* 〉〉 b₂'} {aₑ : [ n ] a₁ ∼〈〈 Aₑ 〉〉 a₂} {aₑ' : [ n ] a₁' ∼〈〈 Aₑ' 〉〉 a₂'}
  {e₁* : [ n ] e₁ ∼〈〈 eqn-cong A₁* B₁* 〉〉 e₁'} {e₂* : [ n ] e₂ ∼〈〈 eqn-cong A₂* B₂* 〉〉 e₂'} {Aₑ* : [ n ] A₁* ∼〈〈 eqn-cong Aₑ Aₑ' 〉〉 A₂*} {eₑ : [ n ] e₁ ∼〈〈 eqn-cong Aₑ Bₑ 〉〉 e₂} {eₑ' : [ n ] e₁' ∼〈〈 eqn-cong Aₑ' Bₑ' 〉〉 e₂'} {Bₑ* : [ n ] B₁* ∼〈〈 eqn-cong Bₑ Bₑ' 〉〉 B₂*} {bₑ : [ n ] b₁ ∼〈〈 Bₑ 〉〉 b₂} {bₑ' : [ n ] b₁' ∼〈〈 Bₑ' 〉〉 b₂'} →
  [ pred n ] a₁* ∼〈〈 eqTTn-cong n aₑ Aₑ* aₑ' 〉〉 a₂* → [ pred n ] e₁* ∼〈〈 eqTTn-cong n eₑ (eqn-cong₂ {n} Aₑ* Bₑ*) eₑ' 〉〉 e₂* → [ pred n ] b₁* ∼〈〈 eqTTn-cong n bₑ Bₑ* bₑ' 〉〉 b₂* →
  [ _ ] eqTTn-cong n a₁* e₁* b₁* ∼〈〈 eqn-cong (eqTTn-cong n aₑ eₑ bₑ) (eqTTn-cong n aₑ' eₑ' bₑ') 〉〉 eqTTn-cong n a₂* e₂* b₂*
eqTTn-cong₂ {hone} = path-cong₂
eqTTn-cong₂ {hzero} _ _ _ = tt
eqTTn-cong₂ {hminusone} _ _ _ = tt
eqTTn-cong₂ {hminustwo} _ _ _ = tt

Refn : ∀ {n} (A : Type n) → Eq A A
Refn {hone} A = Ref A
Refn {hzero} A = Ref₀ A
Refn {hminusone} A = Ref₋₁ A
Refn {hminustwo} A = tt

Refn-cong : ∀ {n} {A B : Type n} (e : Eq A B) → [ _ ] Refn A ∼〈〈 eqn-cong e e 〉〉 Refn B
Refn-cong {hone} e = Ref-cong e
Refn-cong {hzero} e = Ref₀-cong e
Refn-cong {hminusone} e = tt
Refn-cong {hminustwo} e = tt

Refn-cong₂ : ∀ {n : hLevel}
  {A A' B B' : Type n}
  {e : Eq A B} {e' : Eq A' B'} {A* : Eq A A'} {B* : Eq B B'}
  (sq : [ _ ] e ∼〈〈 eqn-cong A* B* 〉〉 e') →
  [ _ ] Refn-cong e ∼〈〈 eqTTn-cong n (Refn-cong A*) (eqn-cong₂ {n} sq sq) (Refn-cong B*) 〉〉 Refn-cong e'
Refn-cong₂ {hone} = Ref-cong₂
Refn-cong₂ {hzero} _ = tt
Refn-cong₂ {hminusone} _ = tt
Refn-cong₂ {hminustwo} _ = tt

refn : ∀ {n : hLevel} {A : Type n} (a : TT A) →
  [ n ] a ∼〈〈 Refn A 〉〉 a
refn {hone} a = ref a
refn {hzero} _ = ref₀
refn {hminusone} _ = tt
refn {hminustwo} _ = tt

refn-cong : ∀ (n : hLevel) {A A' : Type n} (A* : Eq A A') {a : TT A} {a' : TT A'} (a* : [ n ] a ∼〈〈 A* 〉〉 a') → 
  [ pred n ] refn a ∼〈〈 eqTTn-cong n a* (Refn-cong A*) a* 〉〉 refn a'
refn-cong hone A* a* = ref-cong a*
refn-cong hzero A* a* = tt
refn-cong hminusone A* a* = tt
refn-cong hminustwo A* a* = tt

trivial : ∀ {n : hLevel}
  {A B : Type (pred (pred n))}
  (a : TT A) (e : Eq A B) (b : TT B)
  → [ pred (pred n) ] a ∼〈〈 e 〉〉 b
trivial {hone} _ _ _ = tt
trivial {hzero} _ _ _ = tt
trivial {hminusone} _ _ _ = tt
trivial {hminustwo} _ _ _ = tt
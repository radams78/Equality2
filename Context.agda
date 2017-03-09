{-# OPTIONS --rewriting #-}
<<<<<<< HEAD
=======
<<<<<<< HEAD
=======

>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062
module Context where
open import Level
open import Function hiding (_∋_;const)
open import Data.Unit
open import Data.Product
open import FibSetoid
open import Univ.HLevel

<<<<<<< HEAD
=======
postulate _▷_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}
<<<<<<< HEAD

record Setoid (i j : Level) : Set (suc (i ⊔ j)) where
  field
    Els : Set i
    equ : Els → Els → Set j
    reff : ∀ a → equ a a

module Functors {i j k l} (A : Setoid i j) (B : Setoid k l) where
  postulate Functor : Set
  postulate ap : Functor → Setoid.Els A → Setoid.Els B
  postulate ap2 : ∀ (F : Functor) {a} {a'} → Setoid.equ A a a' → Setoid.equ B (ap F a) (ap F a')
  postulate ap2-ref : ∀ {F a} → ap2 F (Setoid.reff A a) ▷ Setoid.reff B (ap F a)

  {-# REWRITE ap2-ref #-}

open Functors

TYPE : hLevel → Setoid _ _
TYPE n = record { 
  Els = Type n ; 
  equ = Eq ; 
  reff = Refn }

data Cx : Set₁
record Square (Γ : Cx) : Set₁
record Cube (Γ : Cx) : Set₁
CONTEXT : Cx → Setoid _ _
record Typeover (n : hLevel) (Γ : Cx) : Set₁
⟦_⟧C : Cx → Set₁
data Functor (Γ : Cx) (n : hLevel) (F : ⟦ Γ ⟧C → Type n) : Set₁
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
_∋_∼〈_〉_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set
EQC₂ : ∀ {Γ} → Square Γ → Set
RefC : ∀ {Γ} (γ : ⟦ Γ ⟧C) → EQC Γ γ γ
RefC-cong : ∀ {Γ} {γ γ' : ⟦ Γ ⟧C} (γ* : EQC Γ γ γ') → EQC₂ (RefC γ) (RefC γ') γ* γ*
=======

>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062
data Cx : Set₁
⟦_⟧C : Cx → Set₁
data Functor (Γ : Cx) (n : hLevel) (F : ⟦ Γ ⟧C → Type n) : Set₁
record Typeover (n : hLevel) (Γ : Cx) : Set₁
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
EQC₂ : ∀ {Γ} {a₁ a₂ b₁ b₂ : ⟦ Γ ⟧C} → EQC Γ a₁ a₂ → EQC Γ b₁ b₂ → EQC Γ a₁ b₁ → EQC Γ a₂ b₂ → Set
CONTEXT : Cx → OneType (suc zero) zero zero
RefC : ∀ {Γ} (γ : ⟦ Γ ⟧C) → EQC Γ γ γ
RefC-cong : ∀ {Γ} {γ γ' : ⟦ Γ ⟧C} (γ* : EQC Γ γ γ') → EQC₂ (RefC γ) (RefC γ') γ* γ*
<<<<<<< HEAD
_∋_∼⟨_⟩_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set
=======
_∋_∼〈_〉_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set

>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : ∀ {n} (Γ : Cx) → Typeover n Γ → Cx

<<<<<<< HEAD
CONTEXT Γ = record {
  graph = record {
    Vertex = ⟦ Γ ⟧C ;
    Path = EQC Γ ;
    ref = RefC };
  isOneType = record {
    Fill = λ γ* → EQC₂ (RefGraph.Square.north γ*) (RefGraph.Square.south γ*) (RefGraph.Square.west γ*) (RefGraph.Square.east γ*) }}

=======
<<<<<<< HEAD
<<<<<<< HEAD
record Square Γ where
  field
    NW : ⟦ Γ ⟧C
    NE : ⟦ Γ ⟧C
    SW : ⟦ Γ ⟧C
    SE : ⟦ Γ ⟧C
    North : EQC Γ NW NE
    South : EQC Γ SW SE
    West  : EQC Γ NW SW
    East  : EQC Γ NE SE

mk-square : ∀ {Γ} {γ₁ γ₂ δ₁ δ₂ : ⟦ Γ ⟧C} → EQC Γ γ₁ γ₂ → EQC Γ δ₁ δ₂ → EQC Γ γ₁ δ₁ → EQC Γ γ₂ δ₂ → Square Γ
mk-square {Γ} {γ₁} {γ₂} {δ₁} {δ₂} γ* δ* e₁ e₂ = record { NW = γ₁; NE = γ₂; SW = δ₁; SE = δ₂; North = γ*; South = δ*; West = e₁; East = e₂}

record Cube Γ where
  field
    top   : Square Γ
    bottom : Square Γ
    nw    : EQC Γ (Square.NW top) (Square.NW bottom)
    ne    : EQC Γ (Square.NE top) (Square.NE bottom)
    sw    : EQC Γ (Square.SW top) (Square.SW bottom)
    se    : EQC Γ (Square.SE top) (Square.SE bottom)

  north : Square Γ
  north = mk-square (Square.North top) (Square.North bottom) nw ne

  south : Square Γ
  south = mk-square (Square.South top) (Square.South bottom) sw se

  west : Square Γ
  west = mk-square (Square.West top) (Square.West bottom) nw sw

  east : Square Γ
  east = mk-square (Square.East top) (Square.East bottom) ne se

CONTEXT Γ = record { 
  Els = ⟦ Γ ⟧C ; 
  equ = EQC Γ ; 
  reff = RefC }

record Typeover n Γ where
  field
    obj : Functor (CONTEXT Γ) (TYPE n)
    obj-cong₂ : ∀ (sq : Square Γ) (sq-fill : EQC₂ sq) → 
      [ n ] ap2 _ _ obj (Square.North sq) ∼〈〈 eqn-cong (ap2 _ _ obj (Square.West sq)) (ap2 _ _ obj (Square.East sq)) 〉〉 ap2 _ _ obj (Square.South sq)
    obj-cong₃ : ∀ (cube : Cube Γ)
      (top-fill : EQC₂ (Cube.top cube))
      (bottom-fill : EQC₂ (Cube.bottom cube))
      (north-fill : EQC₂ (Cube.north cube))
      (south-fill : EQC₂ (Cube.south cube))
      (west-fill : EQC₂ (Cube.west cube))
      (east-fill : EQC₂ (Cube.east cube))
      → [ pred n ] obj-cong₂ (Cube.top cube) top-fill ∼〈〈 eqTTn-cong n (obj-cong₂ _ north-fill) (eqn-cong₂ {A₁* = ap2 _ _ obj (Square.West (Cube.top cube))} (obj-cong₂ _ west-fill) (obj-cong₂ _ east-fill)) (obj-cong₂ _ south-fill) 〉〉 obj-cong₂ _ bottom-fill

⟦ A ⟧T γ = TT (ap _ _ (Typeover.obj A) γ)

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
=======
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062
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

--TODO Refactor
record Typeover n Γ where
  field
    obj : ∀ (γ : ⟦ Γ ⟧C) → Type n
    obj-cong : Functor Γ n obj
    obj-cong₂ : Functor₂ Γ n obj obj-cong
<<<<<<< HEAD
    obj-cong₃ : ∀ {γ δ : OneType.Square (CONTEXT Γ)}
      {enw : EQC Γ (OneType.Square.nw (CONTEXT Γ) γ) (OneType.Square.nw (CONTEXT Γ) δ)}
      {ene : EQC Γ (OneType.Square.ne (CONTEXT Γ) γ) (OneType.Square.ne (CONTEXT Γ) δ)}
      {esw : EQC Γ (OneType.Square.sw (CONTEXT Γ) γ) (OneType.Square.sw (CONTEXT Γ) δ)}
      {ese : EQC Γ (OneType.Square.se (CONTEXT Γ) γ) (OneType.Square.se (CONTEXT Γ) δ)}
      {γsq : OneType.Fill (CONTEXT Γ) γ} {δsq : OneType.Fill (CONTEXT Γ) δ}
      {sq₁ : OneType.Fill (CONTEXT Γ) (record
                                         { nw = OneType.Square.nw (CONTEXT Γ) γ
                                         ; ne = OneType.Square.ne (CONTEXT Γ) γ
                                         ; sw = OneType.Square.nw (CONTEXT Γ) δ
                                         ; se = OneType.Square.ne (CONTEXT Γ) δ
                                         ; north = OneType.Square.north (CONTEXT Γ) γ
                                         ; south = OneType.Square.north (CONTEXT Γ) δ
                                         ; west = enw
                                         ; east = ene
                                         })}
      {sq₂ : OneType.Fill (CONTEXT Γ) (record
                                         { nw = _
                                         ; ne = _
                                         ; sw = _
                                         ; se = _
                                         ; north = OneType.Square.south (CONTEXT Γ) γ
                                         ; south = OneType.Square.south (CONTEXT Γ) δ
                                         ; west = esw
                                         ; east = ese
                                         })}
      {sqₑ : OneType.Fill (CONTEXT Γ) (record
                                         { nw = _
                                         ; ne = _
                                         ; sw = _
                                         ; se = _
                                         ; north = OneType.Square.west (CONTEXT Γ) γ
                                         ; south = OneType.Square.west (CONTEXT Γ) δ
                                         ; west = enw
                                         ; east = esw
                                         })}
      {sqₑ' : OneType.Fill (CONTEXT Γ) (record
                                          { nw = _
                                          ; ne = _
                                          ; sw = _
                                          ; se = _
                                          ; north = OneType.Square.east (CONTEXT Γ) γ
                                          ; south = OneType.Square.east (CONTEXT Γ) δ
                                          ; west = ene
                                          ; east = ese
                                          })} →
      [ pred n ] ap₃ obj-cong₂ _ _ _ _ γsq ∼⟪ eqTTn-cong n (ap₃ obj-cong₂ _ _ _ _ sq₁) (eqn-cong₂ n (ap₃ obj-cong₂ _ _ _ _ sqₑ) (ap₃ obj-cong₂ _ _ _ _ sqₑ')) (ap₃ obj-cong₂ _ _ _ _ sq₂) ⟫ ap₃ obj-cong₂ _ _ _ _ δsq
=======
    obj-cong₃ : ∀ {γ₁ γ₁' γ₂ γ₂' δ₁ δ₁' δ₂ δ₂' : ⟦ Γ ⟧C}
      {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'} {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} {δ₁* : EQC Γ δ₁ δ₁'} {δ₂* : EQC Γ δ₂ δ₂'} {δₑ : EQC Γ δ₁ δ₂} {δₑ' : EQC Γ δ₁' δ₂'} {e₁ : EQC Γ γ₁ δ₁} {e₁' : EQC Γ γ₁' δ₁'} {e₂ : EQC Γ γ₂ δ₂} {e₂' : EQC Γ γ₂' δ₂'}
      (γsq : EQC₂ γ₁* γ₂* γₑ γₑ') (δsq : EQC₂ δ₁* δ₂* δₑ δₑ') (sq₁ : EQC₂ γ₁* δ₁* e₁ e₁') (sq₂ : EQC₂ γ₂* δ₂* e₂ e₂') (sqₑ : EQC₂ γₑ δₑ e₁ e₂) (sqₑ' : EQC₂ γₑ' δₑ' e₁' e₂') →
      [ pred n ] ap₃ obj-cong₂ _ _ _ _ γsq ∼⟪ eqTTn-cong n (ap₃ obj-cong₂ _ _ _ _ sq₁) (eqn-cong₂ n {A₁* = ap₂ obj-cong γₑ} (ap₃ obj-cong₂ _ _ _ _ sqₑ) (ap₃ obj-cong₂ _ _ _ _ sqₑ')) (ap₃ obj-cong₂ _ _ _ _ sq₂) ⟫ ap₃ obj-cong₂ _ _ _ _ δsq
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ

T ∋ a ∼〈 γ* 〉 b = [ _ ] a ∼〈〈 ap2 _ _ (Typeover.obj T) γ* 〉〉 b

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼⟨ γ* ⟩ s'

<<<<<<< HEAD
T ∋ a ∼⟨ γ* ⟩ b = [ _ ] a ∼⟪ ap₂ (Typeover.obj-cong T) γ* ⟫ b
=======
<<<<<<< HEAD
<<<<<<< HEAD
RefC {ε} _ = tt
RefC {Γ ,, T} (γ , t) = RefC γ , refn t

record Squareover {n Γ} (T : Typeover n Γ) (sq : Square Γ) : Set where
  field
    nw : ⟦ T ⟧T (Square.NW sq)
    ne : ⟦ T ⟧T (Square.NE sq)
    sw : ⟦ T ⟧T (Square.SW sq)
    se : ⟦ T ⟧T (Square.SE sq)
    north : T ∋ nw ∼〈 Square.North sq 〉 ne
    south : T ∋ sw ∼〈 Square.South sq 〉 se
    west  : T ∋ nw ∼〈 Square.West sq 〉 sw
    east  : T ∋ ne ∼〈 Square.East sq 〉 se

  Fill : EQC₂ sq → Set
  Fill fill = [ _ ] north ∼〈〈 eqTTn-cong n west (Typeover.obj-cong₂ T sq fill) east 〉〉 south

square-functor : ∀ {Γ Δ} (point : ⟦ Γ ⟧C → ⟦ Δ ⟧C) →
  (∀ {γ} {γ'} → EQC Γ γ γ' → EQC Δ (point γ) (point γ')) →
  Square Γ → Square Δ
square-functor point path sq = record
                                 { NW = point (Square.NW sq)
                                 ; NE = point (Square.NE sq)
                                 ; SW = point (Square.SW sq)
                                 ; SE = point (Square.SE sq)
                                 ; North = path (Square.North sq)
                                 ; South = path (Square.South sq)
                                 ; West = path (Square.West sq)
                                 ; East = path (Square.East sq)
                                 }

proj₁Sq : ∀ {n Γ} {T : Typeover n Γ} → Square (Γ ,, T) → Square Γ
proj₁Sq = square-functor proj₁ proj₁

proj₂Sq : ∀ {n Γ} {T : Typeover n Γ} (sq : Square (Γ ,, T)) → Squareover T (proj₁Sq sq)
proj₂Sq sq = record
               { nw = proj₂ (Square.NW sq)
               ; ne = proj₂ (Square.NE sq)
               ; sw = proj₂ (Square.SW sq)
               ; se = proj₂ (Square.SE sq)
               ; north = proj₂ (Square.North sq)
               ; south = proj₂ (Square.South sq)
               ; west = proj₂ (Square.West sq)
               ; east = proj₂ (Square.East sq)
               }

EQC₂ {ε} _ = ⊤
EQC₂ {_,,_ {n} Γ T} sq =
  Σ[ sq-fill ∈ EQC₂ (proj₁Sq sq) ] Squareover.Fill {T = T} (proj₂Sq sq) sq-fill

module weakening {m n Γ} {T : Typeover m Γ} where
  module weak-Functor (F : Functor (CONTEXT Γ) (TYPE n)) where
    postulate weak-Functor : Functor (CONTEXT (Γ ,, T)) (TYPE n)
    postulate ap-weak-Functor : ∀ γ → ap _ _ weak-Functor γ ▷ ap _ _ F (proj₁ γ)
    {-# REWRITE ap-weak-Functor #-}
    postulate ap2-weak-Functor : ∀ {γ} {γ'} (γ* : EQC (Γ ,, T) γ γ') →
                                 ap2 _ _ weak-Functor γ* ▷ ap2 _ _ F (proj₁ γ*)
    {-# REWRITE ap2-weak-Functor #-}

  open weak-Functor

  weak : Typeover n Γ → Typeover n (Γ ,, T)
  weak S = record { 
    obj = weak-Functor (Typeover.obj S); --λ {(γ , _) → Typeover.obj S γ};
    obj-cong₂ = λ {sq γ* → Typeover.obj-cong₂ S _ (proj₁ γ*) };
    obj-cong₃ = λ {cube (top-fill , _) (bottom-fill , _) (north-fill , _) (south-fill , _) (west-fill , _)
                  (east-fill , _) → Typeover.obj-cong₃ S _ top-fill bottom-fill north-fill south-fill west-fill east-fill} }

open weakening

square-section : ∀ {n Γ} {T : Typeover n Γ}
  (point : ∀ γ → ⟦ T ⟧T γ) →
  (∀ {γ} {γ'} (γ* : EQC Γ γ γ') → T ∋ point γ ∼〈 γ* 〉 point γ') →
  (sq : Square Γ) → Squareover T sq
square-section point path sq = record
                                 { nw = point (Square.NW sq)
                                 ; ne = point (Square.NE sq)
                                 ; sw = point (Square.SW sq)
                                 ; se = point (Square.SE sq)
                                 ; north = path (Square.North sq)
                                 ; south = path (Square.South sq)
                                 ; west = path (Square.West sq)
                                 ; east = path (Square.East sq)
                                 }
=======
=======
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
T ∋ a ∼〈 γ* 〉 b = [ _ ] a ∼⟪ ap₂ (Typeover.obj-cong T) γ* ⟫ b
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

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
<<<<<<< HEAD
  obj-cong₃ = Typeover.obj-cong₃ S }

record Section {n Γ} (T : Typeover n Γ) : Set₁ where
  field
    vertex : ∀ (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
    edge   : ∀ {γ γ'} (γ* : EQC Γ γ γ') → T ∋ vertex γ ∼⟨ γ* ⟩ vertex γ'
    face   : ∀ {γ₁ γ₁' γ₂ γ₂'} {γ₁* : EQC Γ γ₁ γ₁'} {γ₂* : EQC Γ γ₂ γ₂'}
      {γₑ : EQC Γ γ₁ γ₂} {γₑ' : EQC Γ γ₁' γ₂'} (sq-fill : EQC₂ γ₁* γ₂* γₑ γₑ') →
      [ pred n ] edge γ₁* ∼⟪ eqTTn-cong n (edge γₑ) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill) (edge γₑ') ⟫ edge γ₂*
=======
  obj-cong₃ = λ {(γsq , _) (δsq , _) (sq₁ , _) (sq₂ , _) (sqₑ , _) (sqₑ' , _) → Typeover.obj-cong₃ S γsq δsq sq₁ sq₂ sqₑ sqₑ'}}
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

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

<<<<<<< HEAD
⟦_⟧∋-square : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) (sq : Square Γ) → Squareover T sq
⟦ x ⟧∋-square = square-section ⟦ x ⟧∋ ⟦ x ⟧∋-cong

⟦_⟧∋-cong₂ : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) (sq : Square Γ) →
  (sq-fill : EQC₂ {Γ} sq) → Squareover.Fill {T = T} (⟦ x ⟧∋-square sq) sq-fill
⟦ top ⟧∋-cong₂ _ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ _ (γ₂ , _) = ⟦ x ⟧∋-cong₂ _ γ₂
=======
⟦_⟧∋-cong₂ : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {a₁ a₂ b₁ b₂} {a* : EQC Γ a₁ a₂} {b* : EQC Γ b₁ b₂} 
  {p₁ : EQC Γ a₁ b₁} {p₂ : EQC Γ a₂ b₂}
  (sq : EQC₂ {Γ} a* b* p₁ p₂) → 
  [ _ ] ⟦ x ⟧∋-cong a* ∼⟪ eqTTn-cong n (⟦ x ⟧∋-cong p₁) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq) (⟦ x ⟧∋-cong p₂) ⟫ ⟦ x ⟧∋-cong b*
⟦ top ⟧∋-cong₂ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ (γ₂ , _) = ⟦ x ⟧∋-cong₂ γ₂

⟦_⟧V : ∀ {n Γ} {T : Typeover n Γ} → (Γ ∋ T) → Section T
⟦ x ⟧V = record { vertex = ⟦ x ⟧∋ ; edge = ⟦ x ⟧∋-cong ; face = ⟦ x ⟧∋-cong₂ }

K : ∀ n Γ → Type n → Typeover n Γ
K n _ A = record { 
  obj = λ _ → A ; 
  obj-cong = make-Functor (λ _ → Refn A) ;
  obj-cong₂ = make-Functor₂ (λ _ _ _ _ _ → Refn-cong (Refn A)) ;
<<<<<<< HEAD
  obj-cong₃ = Refn-cong₂ {n} (Refn-cong (Refn A)) }

const : ∀ {n Γ} {A : Type n} (a : TT A) → Section (K n Γ A)
const {n} a = record {
  vertex = λ _ → a ;
  edge = λ _ → refn a ;
  face = λ _ → refn-cong {n} (refn a) }

--TODO Replace with Section ∘ EqTypeover
--TODO Remove
postulate dummy : ∀ n {A B : Type (pred n)} {a : TT A} {e : Eq A B} {b : TT B} → [ pred n ] a ∼⟪ e ⟫ b

EqTypeover : ∀ {n Γ} → Typeover n Γ → Typeover n Γ → Typeover n Γ
EqTypeover {n} S T = record {
  obj = λ γ → eqn (Typeover.obj S γ) (Typeover.obj T γ) ;
  obj-cong = make-Functor (λ γ* → eqn-cong (ap₂ (Typeover.obj-cong S) γ*) (ap₂ (Typeover.obj-cong T) γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqn-cong₂ n (ap₃ (Typeover.obj-cong₂ S) _ _ _ _ sq-fill) (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill)) ;
  obj-cong₃ = λ {γ} {δ} {enw} {ene} {esw} {ese} {γsq} {δsq} {sq₁} {sq₂} {sqₑ}
                  {sqₑ'} →
                  eqn-cong₃ n (Typeover.obj-cong₃ S) (Typeover.obj-cong₃ T) }

EqT : ∀ {n Γ} (S T : Typeover n Γ) → Set₁
EqT S T = Section (EqTypeover S T)

EqTypeover-cong : ∀ {n Γ} {S S' T T' : Typeover n Γ} →
  EqT S S' → EqT T T' →
  EqT (EqTypeover S T) (EqTypeover S' T')
EqTypeover-cong {n} S* T* = record {
  vertex = λ γ → eqn-cong (Section.vertex S* γ) (Section.vertex T* γ) ;
  edge = λ γ* → eqn-cong₂ n (Section.edge S* γ*) (Section.edge T* γ*) ;
  face = λ sq-fill → eqn-cong₃ n (Section.face S* sq-fill) (Section.face T* sq-fill) }

refT : ∀ {n Γ} (T : Typeover n Γ) → EqT T T
refT {n} {Γ} T = record {
  vertex = λ γ → Refn (Typeover.obj T γ) ;
  edge = λ γ* → Refn-cong (ap₂ (Typeover.obj-cong T) γ*) ;
  face = λ sq-fill → Refn-cong₂ {n} (ap₃ (Typeover.obj-cong₂ T) _ _ _ _ sq-fill) }

eqS : ∀ {n Γ} {S T : Typeover n Γ} → Section S → EqT S T → Section T → Typeover (pred n) Γ
eqS {n} {Γ} {S} {T} s e t = record {
  obj = λ γ → eqTTn (Section.vertex s γ) (Section.vertex e γ) (Section.vertex t γ) ;
  obj-cong = make-Functor (λ γ* → eqTTn-cong n (Section.edge s γ*) (Section.edge e γ*) (Section.edge t γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face s sq-fill) (Section.face e sq-fill) (Section.face t sq-fill)) ;
  obj-cong₃ = trivial n }

--TODO Fill in
postulate eqS-cong : ∀ {n Γ}
                   {S S' T T' : Typeover n Γ}
                   {S* : EqT S S'} {T* : EqT T T'} {e : Section (EqTypeover S T)} {e' : Section (EqTypeover S' T')}
                   {s : Section S} {s' : Section S'} {t : Section T} {t' : Section T'} →
                   Section (eqS s S* s') → Section (eqS e (EqTypeover-cong S* T*) e') → Section (eqS t T* t') →
                   EqT (eqS s e t) (eqS s' e' t')

refS : ∀ {n Γ} {T : Typeover n Γ} (s : Section T) → Section (eqS s (refT T) s)
refS {n} {Γ} {T} s = record {
  vertex = λ γ → refn (Section.vertex s γ) ;
  edge = λ γ* → refn-cong {n} (Section.edge s γ*) ;
  face = λ _ → trivial n }

--TODO Inline
OneTypeMap : Cx → Cx → Set₁
OneTypeMap Γ Δ = OneTypeFunctor (CONTEXT Γ) (CONTEXT Δ)

record OneTypeMapEq {Γ Δ} (F G : OneTypeMap Γ Δ) : Set₁ where
  field
    vertex : ∀ γ → EQC Δ (app F γ) (app G γ)
    edge : ∀ {γ γ'} (γ* : EQC Γ γ γ') → EQC₂ (vertex γ) (vertex γ') (app₂ F γ*) (app₂ G γ*)

TypeoverF : ∀ {n} {Γ Δ} → OneTypeMap Γ Δ → Typeover n Δ → Typeover n Γ
TypeoverF F T = record {
  obj = λ γ → Typeover.obj T (app F γ) ;
  obj-cong = make-Functor (λ γ* → ap₂ (Typeover.obj-cong T) (app₂ F γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → ap₃ (Typeover.obj-cong₂ T) (app₂ F γ₁*) (app₂ F γ₂*) (app₂ F γₑ) (app₂ F γₑ') (app₃ F sq-fill)) ;
  obj-cong₃ = Typeover.obj-cong₃ T}
=======
  obj-cong₃ = λ _ _ _ _ _ _ → Refn-cong₂ {n} (Refn-cong (Refn A))}
>>>>>>> 70845cfc78c50b862cf0016ffbe2191c6ebdbe31
>>>>>>> a206cc8a33ea749bd2322212ad62b14ee5c09062

Typeover-eq : ∀ {n Γ Δ ⟦ρ⟧ ⟦σ⟧} (T : Typeover n Δ) →
  OneTypeMapEq ⟦ρ⟧ ⟦σ⟧ →
  (F : Section (TypeoverF ⟦ρ⟧ T))
  (G : Section (TypeoverF ⟦σ⟧ T)) →
  Typeover (pred n) Γ
Typeover-eq {n} {⟦ρ⟧ = ⟦ρ⟧} {⟦σ⟧} T ⟦τ⟧ F G = record {
  obj = λ γ → eqTTn (Section.vertex F γ) (ap₂ (Typeover.obj-cong T) (OneTypeMapEq.vertex ⟦τ⟧ γ)) (Section.vertex G γ) ;
  obj-cong = make-Functor (λ {γ} {γ'} γ* → eqTTn-cong n (Section.edge F γ*) (ap₃ (Typeover.obj-cong₂ T) (OneTypeMapEq.vertex ⟦τ⟧ _) (OneTypeMapEq.vertex ⟦τ⟧ _) (app₂ ⟦ρ⟧ γ*) (app₂ ⟦σ⟧ γ*) (OneTypeMapEq.edge ⟦τ⟧ γ*)) (Section.edge G γ*)) ;
  obj-cong₂ = make-Functor₂ (λ γ₁* γ₂* γₑ γₑ' sq-fill → eqTTn-cong₂ n (Section.face F sq-fill) (Typeover.obj-cong₃ T) (Section.face G sq-fill)) ;
  obj-cong₃ = trivial n }

{-# OPTIONS --rewriting #-}
module Context where
open import Level
open import Function hiding (_∋_)
open import Data.Unit
open import Data.Product
open import Univ

postulate _▷_ : ∀ {i} {A : Set i} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}

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
⟦_⟧T : ∀ {n Γ} → Typeover n Γ → ⟦ Γ ⟧C → Set
EQC : ∀ Γ → ⟦ Γ ⟧C → ⟦ Γ ⟧C → Set
_∋_∼〈_〉_ : ∀ {n Γ} (T : Typeover n Γ) {γ γ'} → ⟦ T ⟧T γ → EQC Γ γ γ' → ⟦ T ⟧T γ' → Set
EQC₂ : ∀ {Γ} → Square Γ → Set
RefC : ∀ {Γ} (γ : ⟦ Γ ⟧C) → EQC Γ γ γ

infix 75 _,,_
data Cx where
  ε : Cx
  _,,_ : ∀ {n} (Γ : Cx) → Typeover n Γ → Cx

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

⟦ ε ⟧C = Lift ⊤
⟦ Γ ,, S ⟧C = Σ[ γ ∈ ⟦ Γ ⟧C ] ⟦ S ⟧T γ

T ∋ a ∼〈 γ* 〉 b = [ _ ] a ∼〈〈 ap2 _ _ (Typeover.obj T) γ* 〉〉 b

EQC ε (lift tt) (lift tt) = ⊤
EQC (Γ ,, S) (γ , s) (γ' , s') = Σ[ γ* ∈ EQC Γ γ γ' ] S ∋ s ∼〈 γ* 〉 s'

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

infix 5 _∋_
data _∋_ : ∀ {n} (Γ : Cx) (T : Typeover n Γ) → Set₁ where
  top : ∀ {n Γ} {T : Typeover n Γ} → Γ ,, T  ∋ weak T
  pop : ∀ {m n Γ} {S : Typeover m Γ} {T : Typeover n Γ} → Γ ∋ T → Γ ,, S ∋ weak T

⟦_⟧∋ : ∀ {n Γ} {T : Typeover n Γ} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧T γ
⟦ top ⟧∋ (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ

⟦_⟧∋-cong : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) {γ γ'} (γ* : EQC Γ γ γ') → T ∋ ⟦ x ⟧∋ γ ∼〈 γ* 〉 ⟦ x ⟧∋ γ'
⟦ top ⟧∋-cong (_ , t*) = t*
⟦ pop x ⟧∋-cong (γ* , _) = ⟦ x ⟧∋-cong γ*

⟦_⟧∋-square : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) (sq : Square Γ) → Squareover T sq
⟦ x ⟧∋-square = square-section ⟦ x ⟧∋ ⟦ x ⟧∋-cong

⟦_⟧∋-cong₂ : ∀ {n Γ} {T : Typeover n Γ} (x : Γ ∋ T) (sq : Square Γ) →
  (sq-fill : EQC₂ {Γ} sq) → Squareover.Fill {T = T} (⟦ x ⟧∋-square sq) sq-fill
⟦ top ⟧∋-cong₂ _ (_ , t₂) = t₂
⟦ pop x ⟧∋-cong₂ _ (γ₂ , _) = ⟦ x ⟧∋-cong₂ _ γ₂


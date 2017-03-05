module Univ.Groupoid where
open import FibSetoid
open import Univ.Univ
open import Univ.Sets

-- Groupoids

postulate eqU : U → U → U
_⇔_ : U → U → Set
A ⇔ B = Obj (eqU A B)

postulate eqU-cong : ∀ {A A' B B'} → A ⇔ B → A' ⇔ B' → eqU A A' ⇔ eqU B B'

postulate path : ∀ {A B} → Obj A → A ⇔ B → Obj B → Sets
private _∼⟪_⟫_ : ∀ {A B} → Obj A → A ⇔ B → Obj B → Set
a ∼⟪ φ ⟫ b = El (path a φ b)

--TODO Common pattern with Square
GROUPOID : FibSetoid
GROUPOID = record {
  Dom = U ;
  Fib = Obj ;
  eqG = eqU ;
  eqG-cong = eqU-cong ;
  EqFib = _∼⟪_⟫_ }

--TODO Common pattern
postulate eqU-cong₂ : FibSetoid.HasCong₂ GROUPOID

postulate path-cong : ∀ {A A' B B' a a' b b' φ φ'} {A* : A ⇔ A'} {B* : B ⇔ B'} → 
                    a ∼⟪ A* ⟫ a' → φ ∼⟪ eqU-cong A* B* ⟫ φ' → b ∼⟪ B* ⟫ b' → 
                    path a φ b ≃ path a' φ' b'

--TODO Extract cube type
postulate eqU-cong₃ : ∀ {A B C D : FibSetoid.Square GROUPOID}
                      {F₁ : FibSetoid.Square.nw A ⇔ FibSetoid.Square.nw B} {F₁' : FibSetoid.Square.ne A ⇔ FibSetoid.Square.ne B}
                      {F₂ : FibSetoid.Square.sw A ⇔ FibSetoid.Square.sw B} {F₂' : FibSetoid.Square.se A ⇔ FibSetoid.Square.se B}
                      {G₁ : FibSetoid.Square.nw C ⇔ FibSetoid.Square.nw D} {G₁' : FibSetoid.Square.ne C ⇔ FibSetoid.Square.ne D}
                      {G₂ : FibSetoid.Square.sw C ⇔ FibSetoid.Square.sw D} {G₂' : FibSetoid.Square.se C ⇔ FibSetoid.Square.se D}
                      {H₁ : FibSetoid.Square.nw A ⇔ FibSetoid.Square.nw C} {H₁' : FibSetoid.Square.ne A ⇔ FibSetoid.Square.ne C}
                      {H₂ : FibSetoid.Square.sw A ⇔ FibSetoid.Square.sw C} {H₂' : FibSetoid.Square.se A ⇔ FibSetoid.Square.se C}
                      {K₁ : FibSetoid.Square.nw B ⇔ FibSetoid.Square.nw D} {K₁' : FibSetoid.Square.ne B ⇔ FibSetoid.Square.ne D}
                      {K₂ : FibSetoid.Square.sw B ⇔ FibSetoid.Square.sw D} {K₂' : FibSetoid.Square.se B ⇔ FibSetoid.Square.se D}
                      {Aₑ* : FibSetoid.Square.Fill A}
                      {Bₑ* : FibSetoid.Square.Fill B}
                      {Cₑ* : FibSetoid.Square.Fill C}
                      {Dₑ* : FibSetoid.Square.Fill D}
                      {H₁* : FibSetoid.Square.north A ∼⟪ eqU-cong H₁ H₁' ⟫ FibSetoid.Square.north C}
                      {H₂* : FibSetoid.Square.south A ∼⟪ eqU-cong H₂ H₂' ⟫ FibSetoid.Square.south C}
                      {Hₑ : FibSetoid.Square.west A ∼⟪ eqU-cong H₁ H₂ ⟫ FibSetoid.Square.west C}
                      {Hₑ' : FibSetoid.Square.east A ∼⟪ eqU-cong H₁' H₂' ⟫ FibSetoid.Square.east C}
                      {K₁* : FibSetoid.Square.north B ∼⟪ eqU-cong K₁ K₁' ⟫ FibSetoid.Square.north D}
                      {K₂* : FibSetoid.Square.south B ∼⟪ eqU-cong K₂ K₂' ⟫ FibSetoid.Square.south D}
                      {Kₑ : FibSetoid.Square.west B ∼⟪ eqU-cong K₁ K₂ ⟫ FibSetoid.Square.west D}
                      {Kₑ' : FibSetoid.Square.east B ∼⟪ eqU-cong K₁' K₂' ⟫ FibSetoid.Square.east D} → 
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

postulate Ref-cong₂ : ∀ {A A' B B'} {F : A ⇔ B} {F' : A' ⇔ B'} {A* : A ⇔ A'} {B* : B ⇔ B'} 
                    (F* : F ∼⟪ eqU-cong A* B* ⟫ F') → Ref-cong F ∼⟪ path-cong (Ref-cong A*) (eqU-cong₂ F* F*) (Ref-cong B*) ⟫₀ Ref-cong F'

postulate ref : ∀ {A} a → a ∼⟪ Ref A ⟫ a

postulate ref-cong : ∀ {A B a b} {e : A ⇔ B} (p : a ∼⟪ e ⟫ b) → ref a ∼⟪ path-cong p (Ref-cong e) p ⟫₀ ref b

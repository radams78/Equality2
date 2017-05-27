module Univ.Groupoid where
open import Level
open import Univ.Univ
open import Univ.Sets
open import Semantics.Universe

-- Groupoids

postulate eqU : U → U → U
_⇔_ : U → U → Set
A ⇔ B = Obj (eqU A B)

postulate eqU-cong : ∀ {A A' B B'} → A ⇔ B → A' ⇔ B' → eqU A A' ⇔ eqU B B'

postulate path : ∀ {A B} → Obj A → A ⇔ B → Obj B → Sets
private _∼⟪_⟫_ : ∀ {A B} → Obj A → A ⇔ B → Obj B → Set
a ∼⟪ φ ⟫ b = El (path a φ b)

postulate Ref : ∀ A → A ⇔ A

GROUPOID = record {
  Dom = U ;
  Fib = Obj ;
  eqG = eqU ;
  ref = Ref ;
  eqG-cong = eqU-cong ;
  EqFib = _∼⟪_⟫_ }

--TODO Common pattern
postulate eqU-cong₂ : Universe.HasCong₂ GROUPOID

postulate path-cong : ∀ {A A' B B' a a' b b' φ φ'} {A* : A ⇔ A'} {B* : B ⇔ B'} → 
                    a ∼⟪ A* ⟫ a' → φ ∼⟪ eqU-cong A* B* ⟫ φ' → b ∼⟪ B* ⟫ b' → 
                    path a φ b ≃ path a' φ' b'

--TODO Extract cube type
postulate eqU-cong₃ : ∀ {A B C D : Universe.Square GROUPOID}
                      {H₁ : Universe.Square.nw {r = GROUPOID} A ⇔ Universe.Square.nw {r = GROUPOID} C}
                      {H₁' : Universe.Square.ne {r = GROUPOID} A ⇔ Universe.Square.ne {r = GROUPOID} C}
                      {H₂ : Universe.Square.sw {r = GROUPOID} A ⇔ Universe.Square.sw {r = GROUPOID} C}
                      {H₂' : Universe.Square.se {r = GROUPOID} A ⇔ Universe.Square.se {r = GROUPOID} C}
                      {K₁ : Universe.Square.nw {r = GROUPOID} B ⇔ Universe.Square.nw {r = GROUPOID} D}
                      {K₁' : Universe.Square.ne {r = GROUPOID} B ⇔ Universe.Square.ne {r = GROUPOID} D}
                      {K₂ : Universe.Square.sw {r = GROUPOID} B ⇔ Universe.Square.sw {r = GROUPOID} D}
                      {K₂' : Universe.Square.se {r = GROUPOID} B ⇔ Universe.Square.se {r = GROUPOID} D}
                      {Aₑ* : Universe.Fill GROUPOID A}
                      {Bₑ* : Universe.Fill GROUPOID B}
                      {Cₑ* : Universe.Fill GROUPOID C}
                      {Dₑ* : Universe.Fill GROUPOID D}
                      {H₁* : Universe.Square.north {r = GROUPOID} A ∼⟪ eqU-cong H₁ H₁' ⟫ Universe.Square.north {r = GROUPOID} C}
                      {H₂* : Universe.Square.south {r = GROUPOID} A ∼⟪ eqU-cong H₂ H₂' ⟫ Universe.Square.south {r = GROUPOID} C}
                      {Hₑ : Universe.Square.west {r = GROUPOID} A ∼⟪ eqU-cong H₁ H₂ ⟫ Universe.Square.west {r = GROUPOID} C}
                      {Hₑ' : Universe.Square.east {r = GROUPOID} A ∼⟪ eqU-cong H₁' H₂' ⟫ Universe.Square.east {r = GROUPOID} C}
                      {K₁* : Universe.Square.north {r = GROUPOID} B ∼⟪ eqU-cong K₁ K₁' ⟫ Universe.Square.north {r = GROUPOID} D}
                      {K₂* : Universe.Square.south {r = GROUPOID} B ∼⟪ eqU-cong K₂ K₂' ⟫ Universe.Square.south {r = GROUPOID} D}
                      {Kₑ : Universe.Square.west {r = GROUPOID} B ∼⟪ eqU-cong K₁ K₂ ⟫ Universe.Square.west {r = GROUPOID} D}
                      {Kₑ' : Universe.Square.east {r = GROUPOID} B ∼⟪ eqU-cong K₁' K₂' ⟫ Universe.Square.east {r = GROUPOID} D} → 
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

postulate Ref-cong : ∀ {A B} (F : A ⇔ B) → Ref A ∼⟪ eqU-cong F F ⟫ Ref B

postulate Ref-cong₂ : ∀ {A A' B B'} {F : A ⇔ B} {F' : A' ⇔ B'} {A* : A ⇔ A'} {B* : B ⇔ B'} 
                    (F* : F ∼⟪ eqU-cong A* B* ⟫ F') → Ref-cong F ∼⟪ path-cong (Ref-cong A*) (eqU-cong₂ F* F*) (Ref-cong B*) ⟫₀ Ref-cong F'

postulate ref : ∀ {A} a → a ∼⟪ Ref A ⟫ a

postulate ref-cong : ∀ {A B a b} {e : A ⇔ B} (p : a ∼⟪ e ⟫ b) → ref a ∼⟪ path-cong p (Ref-cong e) p ⟫₀ ref b

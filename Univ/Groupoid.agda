module Univ.Groupoid where
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
record SquareG : Set where
  field
    nw : U
    ne : U
    sw : U
    se : U
    north : nw ⇔ ne
    south : sw ⇔ se
    west  : nw ⇔ sw
    east  : ne ⇔ se

postulate eqU-cong₂ : ∀ {top bottom : SquareG} →
                    SquareG.north top ∼⟪ eqU-cong (SquareG.west top) (SquareG.east top) ⟫ SquareG.south top →
                    SquareG.north bottom ∼⟪ eqU-cong (SquareG.west bottom) (SquareG.east bottom) ⟫ SquareG.south bottom →
                    eqU-cong (SquareG.north top) (SquareG.north bottom) ∼⟪ eqU-cong (eqU-cong (SquareG.west top) (SquareG.west bottom)) (eqU-cong (SquareG.east top) (SquareG.east bottom)) ⟫ eqU-cong (SquareG.south top) (SquareG.south bottom)

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

postulate Ref-cong₂ : ∀ {A A' B B'} {F : A ⇔ B} {F' : A' ⇔ B'} {A* : A ⇔ A'} {B* : B ⇔ B'} 
                    (F* : F ∼⟪ eqU-cong A* B* ⟫ F') → Ref-cong F ∼⟪ path-cong (Ref-cong A*) (eqU-cong₂ F* F*) (Ref-cong B*) ⟫₀ Ref-cong F'

postulate ref : ∀ {A} a → a ∼⟪ Ref A ⟫ a

postulate ref-cong : ∀ {A B a b} {e : A ⇔ B} (p : a ∼⟪ e ⟫ b) → ref a ∼⟪ path-cong p (Ref-cong e) p ⟫₀ ref b


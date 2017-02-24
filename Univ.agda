{-# OPTIONS --rewriting #-}
postulate _↦_ : ∀ {i} {A : Set i} → A → A → Set i
{-# BUILTIN REWRITE _↦_ #-}

module Univ where

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

postulate tt : One

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
_∼〈〈_〉〉₀_ : ∀ {A B} → El A → A ≃ B → El B → Set
a ∼〈〈 e 〉〉₀ b = Prf (eq a e b)

postulate iso-cong₂ : ∀ {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂'}
                    {A₁* : A₁ ≃ A₁'} {B₁* : B₁ ≃ B₁'} {A₂* : A₂ ≃ A₂'} {B₂* : B₂ ≃ B₂'}
                    {Aₑ : A₁ ≃ A₂} {Aₑ' : A₁' ≃ A₂'} {Bₑ : B₁ ≃ B₂} {Bₑ' : B₁' ≃ B₂'} →
                    A₁* ∼〈〈 iso-cong Aₑ Aₑ' 〉〉₀ A₂* → B₁* ∼〈〈 iso-cong Bₑ Bₑ' 〉〉₀ B₂* →
                    iso-cong A₁* B₁* ∼〈〈 iso-cong (iso-cong Aₑ Bₑ) (iso-cong Aₑ' Bₑ') 〉〉₀ iso-cong A₂* B₂*

postulate eq-cong : ∀ {A A' B B' a a' f f' b b'} {A* : A ≃ A'} {B* : B ≃ B'} → 
                  a ∼〈〈 A* 〉〉₀ a' → f ∼〈〈 iso-cong A* B* 〉〉₀ f' → b ∼〈〈 B* 〉〉₀ b' → 
                  eq a f b ↔ eq a' f' b'

postulate Ref₀ : ∀ A → A ≃ A

postulate ref₀ : ∀ {A} {a} → a ∼〈〈 Ref₀ A 〉〉₀ a

-- Groupoids

postulate eqU : U → U → U
_⇔_ : U → U → Set
A ⇔ B = Obj (eqU A B)

postulate eqU-cong : ∀ {A A' B B'} → A ⇔ B → A' ⇔ B' → eqU A A' ⇔ eqU B B'

postulate path : ∀ {A B} → Obj A → A ⇔ B → Obj B → Sets
_∼〈〈_〉〉_ : ∀ {A B} → Obj A → A ⇔ B → Obj B → Set
a ∼〈〈 φ 〉〉 b = El (path a φ b)

postulate eqU-cong₂ : ∀ {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂'}
                    {A₁* : A₁ ⇔ A₁'} {B₁* : B₁ ⇔ B₁'} {A₂* B₂*}
                    {A* : A₁ ⇔ A₂} {A'* : A₁' ⇔ A₂'} {B* : B₁ ⇔ B₂} {B'* : B₁' ⇔ B₂'} → 
                    A₁* ∼〈〈 eqU-cong A* A'* 〉〉 A₂* → B₁* ∼〈〈 eqU-cong B* B'* 〉〉 B₂* → 
                    eqU-cong A₁* B₁* ∼〈〈 eqU-cong (eqU-cong A* B*) (eqU-cong A'* B'*) 〉〉 eqU-cong A₂* B₂*

postulate path-cong : ∀ {A A' B B' a a' b b' φ φ'} {A* : A ⇔ A'} {B* : B ⇔ B'} → 
                    a ∼〈〈 A* 〉〉 a' → φ ∼〈〈 eqU-cong A* B* 〉〉 φ' → b ∼〈〈 B* 〉〉 b' → 
                    path a φ b ≃ path a' φ' b'

postulate eqU-cong₃ : ∀ {A₁ A₁' A₂ A₂' B₁ B₁' B₂ B₂' C₁ C₁' C₂ C₂' D₁ D₁' D₂ D₂' : U} 
                      {A₁* : A₁ ⇔ A₁'} {A₂* : A₂ ⇔ A₂'} {Aₑ : A₁ ⇔ A₂} {Aₑ' : A₁' ⇔ A₂'} 
                      {B₁* : B₁ ⇔ B₁'} {B₂* : B₂ ⇔ B₂'} {Bₑ : B₁ ⇔ B₂} {Bₑ' : B₁' ⇔ B₂'} 
                      {C₁* : C₁ ⇔ C₁'} {C₂* : C₂ ⇔ C₂'} {Cₑ : C₁ ⇔ C₂} {Cₑ' : C₁' ⇔ C₂'} 
                      {D₁* : D₁ ⇔ D₁'} {D₂* : D₂ ⇔ D₂'} {Dₑ : D₁ ⇔ D₂} {Dₑ' : D₁' ⇔ D₂'} 
                      {F₁ : A₁ ⇔ B₁} {F₁' : A₁' ⇔ B₁'} {F₂ : A₂ ⇔ B₂} {F₂' : A₂' ⇔ B₂'}
                      {G₁ : C₁ ⇔ D₁} {G₁' : C₁' ⇔ D₁'} {G₂ : C₂ ⇔ D₂} {G₂' : C₂' ⇔ D₂'}
                      {H₁ : A₁ ⇔ C₁} {H₁' : A₁' ⇔ C₁'} {H₂ : A₂ ⇔ C₂} {H₂' : A₂' ⇔ C₂'}
                      {K₁ : B₁ ⇔ D₁} {K₁' : B₁' ⇔ D₁'} {K₂ : B₂ ⇔ D₂} {K₂' : B₂' ⇔ D₂'}
                      {Aₑ* : A₁* ∼〈〈 eqU-cong Aₑ Aₑ' 〉〉 A₂*}
                      {Bₑ* : B₁* ∼〈〈 eqU-cong Bₑ Bₑ' 〉〉 B₂*}
                      {Cₑ* : C₁* ∼〈〈 eqU-cong Cₑ Cₑ' 〉〉 C₂*}
                      {Dₑ* : D₁* ∼〈〈 eqU-cong Dₑ Dₑ' 〉〉 D₂*}
                      {H₁* : A₁* ∼〈〈 eqU-cong H₁ H₁' 〉〉 C₁*}
                      {H₂* : A₂* ∼〈〈 eqU-cong H₂ H₂' 〉〉 C₂*}
                      {Hₑ : Aₑ ∼〈〈 eqU-cong H₁ H₂ 〉〉 Cₑ}
                      {Hₑ' : Aₑ' ∼〈〈 eqU-cong H₁' H₂' 〉〉 Cₑ'}
                      {K₁* : B₁* ∼〈〈 eqU-cong K₁ K₁' 〉〉 D₁*}
                      {K₂* : B₂* ∼〈〈 eqU-cong K₂ K₂' 〉〉 D₂*}
                      {Kₑ : Bₑ ∼〈〈 eqU-cong K₁ K₂ 〉〉 Dₑ}
                      {Kₑ' : Bₑ' ∼〈〈 eqU-cong K₁' K₂' 〉〉 Dₑ'} → 
                      Aₑ* ∼〈〈 path-cong H₁* (eqU-cong₂ Hₑ Hₑ') H₂* 〉〉₀ Cₑ* → 
                      Bₑ* ∼〈〈 path-cong K₁* (eqU-cong₂ Kₑ Kₑ') K₂* 〉〉₀ Dₑ* → 
                      eqU-cong₂ Aₑ* Bₑ* ∼〈〈 path-cong (eqU-cong₂ H₁* K₁*) (eqU-cong₂ (eqU-cong₂ Hₑ Kₑ) (eqU-cong₂ Hₑ' Kₑ')) (eqU-cong₂ H₂* K₂*) 〉〉₀ eqU-cong₂ Cₑ* Dₑ*

postulate Ref : ∀ A → A ⇔ A

postulate Ref-cong : ∀ {A B} (F : A ⇔ B) → Ref A ∼〈〈 eqU-cong F F 〉〉 Ref B

postulate Ref-cong₂ : ∀ {A A' B B'} {F : A ⇔ B} {F' : A' ⇔ B'} {A* : A ⇔ A'} {B* : B ⇔ B'} 
                    (F* : F ∼〈〈 eqU-cong A* B* 〉〉 F') → Ref-cong F ∼〈〈 path-cong (Ref-cong A*) (eqU-cong₂ F* F*) (Ref-cong B*) 〉〉₀ Ref-cong F'

postulate ref : ∀ {A} a → a ∼〈〈 Ref A 〉〉 a

postulate ref-cong : ∀ {A B a b} {e : A ⇔ B} (p : a ∼〈〈 e 〉〉 b) → ref a ∼〈〈 path-cong p (Ref-cong e) p 〉〉₀ ref b


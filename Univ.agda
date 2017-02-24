module Univ where

postulate U : Set
postulate El : U → Set

postulate One : U
postulate TT : El One

postulate Prop : U
postulate ONE : El Prop
postulate IFF : El Prop → El Prop → El Prop

postulate Sets : U
postulate PROP : El Sets

postulate EqU : U → U → U
_≃_ : U → U → Set
A ≃ B = El (EqU A B)

postulate Ref : ∀ A → A ≃ A
postulate EqU-cong : ∀ {A A' B B'} → A ≃ A' → B ≃ B' → EqU A B ≃ EqU A' B'

postulate EqEl : ∀ {A B} → El A → A ≃ B → El B → U
_∼〈〈_〉〉_ : ∀ {A B} → El A → A ≃ B → El B → Set
a ∼〈〈 e 〉〉 b = El (EqEl a e b)

postulate Ref₂ : ∀ A → Ref A ∼〈〈 EqU-cong (Ref A) (Ref A) 〉〉 Ref A
--Redundant if we add the rule EqU-cong (Ref A) (Ref B) = Ref (A ≃ B)

postulate EqU-cong₂ : ∀ {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂'}
                    {A₁* : A₁ ≃ A₁'} {B₁* : B₁ ≃ B₁'} {A₂* B₂*}
                    {A* : A₁ ≃ A₂} {A'* : A₁' ≃ A₂'} {B* : B₁ ≃ B₂} {B'* : B₁' ≃ B₂'} → 
                    A₁* ∼〈〈 EqU-cong A* A'* 〉〉 A₂* → B₁* ∼〈〈 EqU-cong B* B'* 〉〉 B₂* → 
                    EqU-cong A₁* B₁* ∼〈〈 EqU-cong (EqU-cong A* B*) (EqU-cong A'* B'*) 〉〉 EqU-cong A₂* B₂*

postulate EqEl-cong : ∀ {A A' B B' a a' γ γ' b b'}
                      {A* : A ≃ A'} {B* : B ≃ B'} → 
                      a ∼〈〈 A* 〉〉 a' → γ ∼〈〈 EqU-cong A* B* 〉〉 γ' → b ∼〈〈 B* 〉〉 b' → 
                      EqEl a γ b ≃ EqEl a' γ' b'

postulate EqEl-cong₂ : ∀ {A₁ A₁' B₁ B₁' a₁ a₁' γ₁ γ₁' b₁ b₁'
                       A₂ A₂' B₂ B₂' a₂ a₂' γ₂ γ₂' b₂ b₂'} 
                       {A₁* : A₁ ≃ A₁'} {B₁* : B₁ ≃ B₁'} 
                       {a₁* : a₁ ∼〈〈 A₁* 〉〉 a₁'} {γ₁* : γ₁ ∼〈〈 EqU-cong A₁* B₁* 〉〉 γ₁'} {b₁* : b₁ ∼〈〈 B₁* 〉〉 b₁'}
                       {A₂* : A₂ ≃ A₂'} {B₂* : B₂ ≃ B₂'} 
                       {a₂* : a₂ ∼〈〈 A₂* 〉〉 a₂'} {γ₂* : γ₂ ∼〈〈 EqU-cong A₂* B₂* 〉〉 γ₂'} {b₂* : b₂ ∼〈〈 B₂* 〉〉 b₂'}
                       {A* : A₁ ≃ A₂} {B* : B₁ ≃ B₂} {a* : a₁ ∼〈〈 A* 〉〉 a₂} {γ* : γ₁ ∼〈〈 EqU-cong A* B* 〉〉 γ₂} {b* : b₁ ∼〈〈 B* 〉〉 b₂} →
                       {A'* : A₁' ≃ A₂'} {B'* : B₁' ≃ B₂'} {a'* : a₁' ∼〈〈 A'* 〉〉 a₂'} {γ'* : γ₁' ∼〈〈 EqU-cong A'* B'* 〉〉 γ₂'} {b'* : b₁' ∼〈〈 B'* 〉〉 b₂'} →
                       {P : A₁* ∼〈〈 EqU-cong A* A'* 〉〉 A₂*} {Q : B₁* ∼〈〈 EqU-cong B* B'* 〉〉 B₂*} → 
                       a₁* ∼〈〈 EqEl-cong a* P a'* 〉〉 a₂* →
                       γ₁* ∼〈〈 EqEl-cong γ* (EqU-cong₂ P Q) γ'* 〉〉 γ₂* → 
                       b₁* ∼〈〈 EqEl-cong b* Q b'* 〉〉 b₂* →
                       EqEl-cong a₁* γ₁* b₁* ∼〈〈 EqU-cong (EqEl-cong a* γ* b*) (EqEl-cong a'* γ'* b'*) 〉〉 EqEl-cong a₂* γ₂* b₂*
--TODO General notion of functor, 2-functor

postulate ref : ∀ {A a} → a ∼〈〈 Ref A 〉〉  a
postulate ref₂ : ∀ {A a} → ref {A} {a} ∼〈〈 EqEl-cong ref (Ref₂ A) ref 〉〉 ref
--Redundant if we add EqEl-cong ref Ref ref = ref

postulate IFF-cong : ∀ {φ φ' ψ ψ'} → φ ∼〈〈 Ref Prop 〉〉 φ' → ψ ∼〈〈 Ref Prop 〉〉 ψ' → IFF φ ψ ∼〈〈 Ref Prop 〉〉 IFF φ' ψ'
postulate IFF-cong₂ : ∀ {φ₁ φ₁' ψ₁ ψ₁' φ₂ φ₂' ψ₂ ψ₂'} {φ₁* : φ₁ ∼〈〈 Ref Prop 〉〉 φ₁'} {ψ₁* : ψ₁ ∼〈〈 Ref Prop 〉〉 ψ₁'} {φ₂* : φ₂ ∼〈〈 Ref Prop 〉〉 φ₂'} {ψ₂* : ψ₂ ∼〈〈 Ref Prop 〉〉 ψ₂'} {φ* φ'* ψ* ψ'*} →
                      φ₁* ∼〈〈 EqEl-cong φ* (Ref₂ Prop) φ'* 〉〉 φ₂* → ψ₁* ∼〈〈 EqEl-cong ψ* (Ref₂ Prop) ψ'* 〉〉 ψ₂* → IFF-cong φ₁* ψ₁* ∼〈〈 EqEl-cong (IFF-cong φ* ψ*) (Ref₂ Prop) (IFF-cong φ'* ψ'*) 〉〉 IFF-cong φ₂* ψ₂*
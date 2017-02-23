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

postulate EqEl-cong : ∀ {A A' B B' a a' γ γ' b b'}
                      (A* : A ≃ A') (B* : B ≃ B') → 
                      a ∼〈〈 A* 〉〉 a' → γ ∼〈〈 EqU-cong A* B* 〉〉 γ' → b ∼〈〈 B* 〉〉 b' → 
                      EqEl a γ b ≃ EqEl a' γ' b'

postulate ref : ∀ {A a} → a ∼〈〈 Ref A 〉〉  a
postulate IFF-cong : ∀ {φ φ' ψ ψ'} → φ ∼〈〈 Ref Prop 〉〉 φ' → ψ ∼〈〈 Ref Prop 〉〉 ψ' → IFF φ ψ ∼〈〈 Ref Prop 〉〉 IFF φ' ψ'
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
postulate EqEl : ∀ {A B} → El A → El (EqU A B) → El B → U
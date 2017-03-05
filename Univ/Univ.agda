module Univ.Univ where

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

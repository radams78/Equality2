module Setoid where

record Setoid : Set₁ where
  field
    Dom : Set
    _≡_ : Dom → Dom → Set
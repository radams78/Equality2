module Univ.Prop where
open import Univ.Univ

-- Propositions

postulate iff : Prp → Prp → Prp
_↔_ : Prp → Prp → Set
φ ↔ ψ = Prf (iff φ ψ)

postulate iff-cong : ∀ {φ φ' ψ ψ'} → φ ↔ φ' → ψ ↔ ψ' → iff φ ψ ↔ iff φ' ψ'

postulate Ref₋₁ : ∀ φ → φ ↔ φ

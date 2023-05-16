module Definitions.Logic where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Definitions.Pair
open import Definitions.Either

infix 3 ¬_

data ⊥ : Set where 

private
    variable
        ℓ ℓA ℓB : Level

¬_ : Set ℓ → Set ℓ
¬ P = P → ⊥

ByContradiction : Set ℓ → Set ℓ
ByContradiction P = ¬ (¬ P)

by-contradiction-by-example : (P : Set ℓ) → P → ByContradiction P
by-contradiction-by-example _ p contr = contr p

∃ : (A : Set ℓA) → (B : A → Set ℓB) → Set (ℓA ⊔ ℓB)
∃ = Σ

_∧_ : Set ℓA → Set ℓB → Set (ℓA ⊔ ℓB)
_∧_ = _×_

_∨_ : Set ℓA → Set ℓB → Set (ℓA ⊔ ℓB)
_∨_ = Either 

infixr 2 _∧_ 
infixr 2 _∨_
module Definitions.Ringoid where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Function.Binary

open Setoid {{...}}

private
    variable
        ℓA ℓ=A : Level 

record Ringoid {A : Set ℓA} {{SA : Setoid ℓ=A A}} (_+_ : BinOp A) (_*_ : BinOp A) : Set (lsuc ℓ=A ⊔ ℓA) where
    field
        left-distribute : (a b c : A) → a * (b + c) ≅ (a * b) + (a * c)
        right-distribute : (a b c : A) → (a + b) * c ≅ (a * c) + (b * c)
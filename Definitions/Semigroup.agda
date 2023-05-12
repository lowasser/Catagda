module Definitions.Semigroup where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record Semigroup {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) : Set (lsuc ℓ) where
    field
        overlap {{base-magma}} : Magma _∙_
        {{is-associative}} : IsAssociative _∙_
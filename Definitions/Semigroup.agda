module Definitions.Semigroup where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record Semigroup {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-magma}} : Magma {ℓS} {ℓ=S} _∙_
        {{is-associative}} : IsAssociative _∙_

make-semigroup : {ℓS ℓ=S : Level} {S : Set ℓS} → (_∙_ : BinOp S) → {{MS : Magma {ℓS} {ℓ=S} _∙_}} → Associate _∙_ → Semigroup _∙_
make-semigroup _ assoc = record {is-associative = record {associate = assoc}}
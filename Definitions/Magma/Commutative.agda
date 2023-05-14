module Definitions.Magma.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record CommutativeMagma {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-magma}} : Magma {ℓS} {ℓ=S} _∙_
        {{is-commutative}} : IsCommutative _∙_
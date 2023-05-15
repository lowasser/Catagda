module Definitions.Magma.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid

record CommutativeMagma {ℓS ℓ=S : Level} {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-magma}} : Magma _∙_
        {{is-commutative}} : IsCommutative _∙_
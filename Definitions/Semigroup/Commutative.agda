module Definitions.Semigroup.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record CommutativeSemigroup {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        {{commutative-magma}} : CommutativeMagma {ℓS} {ℓ=S} _∙_
        overlap {{base-semigroup}} : Semigroup {ℓS} {ℓ=S} _∙_
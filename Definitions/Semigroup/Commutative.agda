module Definitions.Semigroup.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid

private
    variable
        ℓS ℓ=S : Level

record CommutativeSemigroup {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        {{commutative-magma}} : CommutativeMagma _∙_
        overlap {{base-semigroup}} : Semigroup _∙_
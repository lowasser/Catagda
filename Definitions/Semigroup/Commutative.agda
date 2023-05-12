module Definitions.Semigroup.Commutative where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record CommutativeSemigroup {ℓ : Level} {S : Set ℓ} (_∙_ : BinOp S) : Set (lsuc ℓ) where
    field
        {{commutative-magma}} : CommutativeMagma _∙_
        overlap {{base-semigroup}} : Semigroup _∙_
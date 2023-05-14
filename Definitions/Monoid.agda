module Definitions.Monoid where

open import Agda.Primitive
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties

record Monoid {ℓS ℓ=S : Level} {S : Set ℓS} (_∙_ : BinOp S) (i : S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-semigroup}} : Semigroup {ℓS} {ℓ=S} _∙_
        overlap {{has-identity}} : HasIdentity _∙_ i

make-monoid : {ℓS ℓ=S : Level} {S : Set ℓS} → (_∙_ : BinOp S) → {{SM : Semigroup {ℓS} {ℓ=S} _∙_}} → (i : S) → LeftIdentity _∙_ i → RightIdentity _∙_ i → Monoid _∙_ i
make-monoid _ _ left-id right-id = record {has-identity = record {left-identity = left-id; right-identity = right-id}}
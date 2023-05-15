module Definitions.Monoid where

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

record Monoid {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) (i : S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-semigroup}} : Semigroup _∙_
        overlap {{has-identity}} : HasIdentity _∙_ i

make-monoid : {S : Set ℓS} → {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{SM : Semigroup _∙_}} → (i : S) → LeftIdentity _∙_ i → RightIdentity _∙_ i → Monoid _∙_ i
make-monoid _ _ left-id right-id = record {has-identity = record {left-identity = left-id; right-identity = right-id}}
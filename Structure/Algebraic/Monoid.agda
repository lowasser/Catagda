module Structure.Algebraic.Monoid where

open import Agda.Primitive
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

private
    variable
        ℓS ℓ=S : Level

record Monoid {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) (i : S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-semigroup}} : Semigroup _∙_
        overlap {{has-identity}} : HasIdentity _∙_ i

make-monoid : {S : Set ℓS} → {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{SM : Semigroup _∙_}} → (i : S) → LeftIdentity _∙_ i → RightIdentity _∙_ i → Monoid _∙_ i
make-monoid _ _ left-id right-id = record {has-identity = record {left-identity = left-id; right-identity = right-id}}
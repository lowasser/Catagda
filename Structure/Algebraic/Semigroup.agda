module Structure.Algebraic.Semigroup where

open import Agda.Primitive
open import Structure.Algebraic.Magma
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

private
    variable
        ℓS ℓ=S : Level

record Semigroup {S : Set ℓS} {{SS : Setoid ℓ=S S}} (_∙_ : BinOp S) : Set (ℓS ⊔ lsuc ℓ=S) where
    field
        overlap {{base-magma}} : Magma _∙_
        overlap {{is-associative}} : IsAssociative _∙_

make-semigroup : {S : Set ℓS} → {{SS : Setoid ℓ=S S}} → (_∙_ : BinOp S) → {{MS : Magma {{SS}} _∙_}} → Associate _∙_ → Semigroup _∙_
make-semigroup _ assoc = record {is-associative = record {associate = assoc}}
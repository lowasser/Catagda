open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

module Structure.Algebraic.Magma.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    {{∙-bi-congruent : BiCongruent _∙_}}
    where

open import Structure.Algebraic.Magma

instance
    ∙-magma : Magma _∙_
    ∙-magma = record {}
open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

module Structure.Algebraic.Semigroup.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    {{∙-bi-congruent : BiCongruent _∙_}}
    (∙-assoc : Associate _∙_)
    where

open import Structure.Algebraic.Magma.Instance _∙_ public
open import Structure.Algebraic.Semigroup

instance
    ∙-is-associative : IsAssociative _∙_
    ∙-is-associative = record {associate = ∙-assoc}

    ∙-semigroup : Semigroup _∙_
    ∙-semigroup = record {}
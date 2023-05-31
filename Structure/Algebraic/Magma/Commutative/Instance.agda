open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

module Structure.Algebraic.Magma.Commutative.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (∙-left-congruent : LeftCongruent _∙_)
    (∙-commute : Commute _∙_)
    where

open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative

instance
    ∙-is-commutative : IsCommutative _∙_
    ∙-is-commutative = record {commute = ∙-commute}

    ∙-bi-congruent : BiCongruent _∙_
    ∙-bi-congruent = bi-congruent-commute _∙_ ∙-left-congruent

    ∙-magma : Magma _∙_
    ∙-magma = record {}

    ∙-commutative-magma : CommutativeMagma _∙_
    ∙-commutative-magma = record {}
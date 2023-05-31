open import Agda.Primitive
open import Function.Unary.Properties
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

open Setoid {{...}}

module Structure.Algebraic.Group.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    (inv : A → A)
    {{∙-bi-congruent : BiCongruent _∙_}}
    (∙-assoc : Associate _∙_)
    (∙-left-identity : LeftIdentity _∙_ i)
    (∙-right-identity : RightIdentity _∙_ i)
    (inv-congruent : Congruent inv)
    (∙-left-inverse : (a : A) → inv a ∙ a ≅ i)
    (∙-right-inverse : (a : A) → a ∙ inv a ≅ i)
    where

open import Structure.Algebraic.Monoid.Instance _∙_ i ∙-assoc ∙-left-identity ∙-right-identity public
open import Structure.Algebraic.Group

instance
    inv-is-congruent : IsCongruent inv
    inv-is-congruent = record {congruent = inv-congruent}

    ∙-has-inverse : HasInverse _∙_ i inv
    ∙-has-inverse = record {left-inverse = ∙-left-inverse; right-inverse = ∙-right-inverse}

    ∙-group : Group _∙_ i inv
    ∙-group = record {}

    ∙-bi-injective : BiInjective _∙_
    ∙-bi-injective = Group.bi-injective ∙-group

    inv-self-inverse : SelfInverse inv
    inv-self-inverse = Group.inverse-self-inverse ∙-group
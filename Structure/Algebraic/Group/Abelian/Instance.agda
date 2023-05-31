open import Agda.Primitive
open import Function.Unary.Properties
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid

open Setoid {{...}}

module Structure.Algebraic.Group.Abelian.Instance
    {ℓA ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    (inv : A → A)
    (∙-left-congruent : LeftCongruent _∙_)
    (∙-commute : Commute _∙_)
    (∙-assoc : Associate _∙_)
    (∙-left-identity : LeftIdentity _∙_ i)
    (inv-congruent : Congruent inv)
    (∙-left-inverse : (a : A) → inv a ∙ a ≅ i)
    where

open import Structure.Algebraic.Monoid.Commutative.Instance _∙_ i ∙-left-congruent ∙-commute ∙-assoc ∙-left-identity public
open import Structure.Algebraic.Group
open import Structure.Algebraic.Group.Abelian

instance
    inv-is-congruent : IsCongruent inv
    inv-is-congruent = record {congruent = inv-congruent}

    ∙-has-inverse : HasInverse _∙_ i inv
    ∙-has-inverse = has-inverse-commute ∙-left-inverse

    ∙-group : Group _∙_ i inv
    ∙-group = record {}

    ∙-abelian-group : AbelianGroup _∙_ i inv
    ∙-abelian-group = record {}
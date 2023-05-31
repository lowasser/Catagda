open import Agda.Primitive
open import Function.Binary
open import Structure.Setoid
open import Structure.Algebraic.Group

module Structure.Algebraic.Group.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    (inv : A → A)
    {{M∙ : Group _∙_ i inv}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    (pi : P i)
    (pinv : (a : A) → P a → P (inv a))
    where

open import Structure.Restricted
open Group {{...}}

open import Function.Unary.Properties
open import Function.Binary.Properties
open import Structure.Algebraic.Monoid.Restricted _∙_ i P combine pi public

restricted-inverse : A RestrictedTo P → A RestrictedTo P
restricted-inverse (a constraint pa) = (inv a) constraint (pinv a pa)

private
    left-inverse : LeftInverse restricted-op restricted-identity restricted-inverse
    left-inverse (a constraint pa) = eq-restricted (left-inverse-on _∙_ i inv a)

    right-inverse : RightInverse restricted-op restricted-identity restricted-inverse
    right-inverse (a constraint pa) = eq-restricted (right-inverse-on _∙_ i inv a)

    inverse-congruent : Congruent restricted-inverse
    inverse-congruent (eq-restricted a=b) = eq-restricted (congruent-on inv a=b)

instance
    restricted-inverse-is-congruent : IsCongruent restricted-inverse
    restricted-inverse-is-congruent = record {congruent = inverse-congruent}

    restricted-has-inverse : HasInverse restricted-op restricted-identity restricted-inverse
    restricted-has-inverse = record {left-inverse = left-inverse; right-inverse = right-inverse}

    restricted-group : Group restricted-op restricted-identity restricted-inverse
    restricted-group = record {}
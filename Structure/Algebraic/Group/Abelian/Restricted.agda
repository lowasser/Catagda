open import Agda.Primitive
open import Function.Binary
open import Structure.Setoid
open import Structure.Algebraic.Group.Abelian

module Structure.Algebraic.Group.Abelian.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    (i : A)
    (inv : A → A)
    {{CSG∙ : AbelianGroup _∙_ i inv}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    (pi : P i)
    (pinv : (a : A) → P a → P (inv a))
    where

open import Structure.Restricted
open AbelianGroup {{...}}

open import Function.Binary.Properties
open import Structure.Algebraic.Group.Restricted _∙_ i inv P combine pi pinv public
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Monoid.Commutative

private 
    commute : Commute restricted-op
    commute (a constraint pa) (b constraint pb) = eq-restricted (commute-on _∙_ a b)

instance
    restricted-op-is-commutative : IsCommutative restricted-op
    restricted-op-is-commutative = record {commute = commute}

    restricted-op-commutative-magma : CommutativeMagma restricted-op
    restricted-op-commutative-magma = record {}

    restricted-commutative-semigroup : CommutativeSemigroup restricted-op
    restricted-commutative-semigroup = record {}

    restricted-commutative-monoid : CommutativeMonoid restricted-op restricted-identity
    restricted-commutative-monoid = record {}

    restricted-abelian-group : AbelianGroup restricted-op restricted-identity restricted-inverse
    restricted-abelian-group = record {}
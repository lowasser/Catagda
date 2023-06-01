open import Agda.Primitive
open import Function.Binary
open import Structure.Setoid
open import Structure.Algebraic.Semigroup

module Structure.Algebraic.Semigroup.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    {{SG∙ : Semigroup _∙_}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    where

open import Structure.Restricted
open import Structure.Setoid.Restricted A P
open Semigroup {{...}}

open import Function.Binary.Properties
open import Structure.Algebraic.Magma.Restricted _∙_ P combine public

private
    assoc : Associate restricted-op
    assoc (a constraint _) (b constraint _) (c constraint _) = eq-restricted (associate-on _∙_ a b c)

instance
    restricted-op-is-associative : IsAssociative restricted-op
    restricted-op-is-associative = record { associate = assoc }

    restricted-op-semigroup : Semigroup restricted-op
    restricted-op-semigroup = record {}
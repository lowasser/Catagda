open import Agda.Primitive
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Setoid
open import Structure.Algebraic.Magma

module Structure.Algebraic.Magma.Restricted 
    {ℓA ℓP ℓ=A : Level}
    {A : Set ℓA}
    {{SA : Setoid ℓ=A A}}
    (_∙_ : BinOp A)
    {{M∙ : Magma _∙_}}
    (P : A → Set ℓP)
    (combine : (a b : A) → P a → P b → P (a ∙ b))
    where

open import Structure.Restricted
open import Structure.Setoid.Restricted A P public
open Magma {{...}}

restricted-op : BinOp (A RestrictedTo P)
restricted-op (a constraint pa) (b constraint pb) = (a ∙ b) constraint (combine a b pa pb)

instance
    restricted-bi-congruent : BiCongruent restricted-op
    restricted-bi-congruent = record {left-congruent = left-cong; right-congruent = right-cong} where
        left-cong : LeftCongruent restricted-op
        left-cong {_ constraint _} (eq-restricted a=b) = eq-restricted (left-congruent-on _∙_ a=b)

        right-cong : RightCongruent restricted-op
        right-cong {_ constraint _} (eq-restricted a=b) = eq-restricted (right-congruent-on _∙_ a=b)

open import Structure.Algebraic.Magma.Instance restricted-op public
open import Agda.Primitive
open import Structure.Setoid

module Data.List.Properties {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Data.List renaming (_::_ to _?::_)
open import Data.List.Setoid {ℓA} {ℓ=A} (A)
open import Relation.Properties
open import Function.Unary.Properties
open import Function.Binary.Properties 

open Setoid {{...}}
open Equivalence {{...}}
open PreOrder {{...}}
open IsReflexive {{...}}

private
    _::_ : A → [ A ] → [ A ]
    _::_ = _?::_

    ::-left-congruent : LeftCongruent _::_
    ::-left-congruent {x} xs≅ys = cons=[]=cons (reflexive x) xs≅ys

    ::-right-congruent : RightCongruent _::_
    ::-right-congruent {xs} x≅y = cons=[]=cons x≅y (reflexive-on [ A ] xs)

    ::-left-injective : (a : A) → Injective (a ::_)
    ::-left-injective _ {xs} {ys} (cons=[]=cons _ xs≅ys) = xs≅ys

    ::-right-injective : (xs : [ A ]) → Injective (_:: xs)
    ::-right-injective _ {x} {y} (cons=[]=cons x≅y _) = x≅y

instance
    ::-bi-congruent : BiCongruent _::_
    ::-bi-congruent = record {left-congruent = ::-left-congruent; right-congruent = ::-right-congruent } 

    ::-bi-injective : BiInjective _::_
    ::-bi-injective = record {left-injective = ::-left-injective; right-injective = ::-right-injective }
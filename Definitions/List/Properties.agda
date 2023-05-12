open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Properties {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} where

open import Definitions.List
open import Definitions.List.Setoid(A)
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties 

private
    ::-left-congruent : LeftCongruent (_::_ {ℓ} {A})
    ::-left-congruent {x} xs≈ys = cons=[]=cons (reflexive-on A x) xs≈ys

    ::-right-congruent : RightCongruent (_::_ {ℓ} {A})
    ::-right-congruent {xs} x≈y = cons=[]=cons x≈y (reflexive-on [ A ] xs)

    ::-left-injective : (a : A) → Injective (a ::_)
    ::-left-injective _ {xs} {ys} (cons=[]=cons _ xs≈ys) = xs≈ys

    ::-right-injective : (xs : [ A ]) → Injective (_:: xs)
    ::-right-injective _ {x} {y} (cons=[]=cons x≈y _) = x≈y

instance
    ::-bi-congruent : BiCongruent (_::_ {ℓ} {A})
    ::-bi-congruent = record {left-congruent = ::-left-congruent; right-congruent = ::-right-congruent } 

    ::-bi-injective : BiInjective (_::_ {ℓ} {A})
    ::-bi-injective = record {left-injective = ::-left-injective; right-injective = ::-right-injective }
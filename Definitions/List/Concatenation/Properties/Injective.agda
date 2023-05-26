open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Concatenation.Properties.Injective {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Definitions.List
open import Definitions.Function.Unary.Properties
open import Definitions.List.Setoid A {{SA}}
open import Definitions.Setoid.Equation
open import Definitions.Function.Binary.Properties
open import Definitions.List.Concatenation.Properties A {{SA}}
open import Definitions.Logic
open import Definitions.List.Length A {{SA}}
open import Definitions.Nat
open import Definitions.Nat.Base
open import Definitions.List.Properties A {{SA}}

private
    ++-left-injective : (xs : [ A ]) → Injective (xs ++_)
    ++-left-injective [] ys≅zs = ys≅zs
    ++-left-injective (x :: xs) (cons=[]=cons _ xsys≅xszs) = ++-left-injective xs xsys≅xszs

    ++-right-injective : (xs : [ A ]) → Injective (_++ xs)
    ++-right-injective xs {y :: ys} {[]} eq = contradiction-implies-anything (nat-not-nonzero-plus-itself (length ys) (length xs) (begin≅
        suc (length ys) + length xs     ≅<>
        length (y :: ys) + length xs    ≅< symmetric-on ℕ (length-distributes-over-++ (y :: ys) xs) >
        length ((y :: ys) ++ xs)        ≅< equal-implies-equal-lengths eq >
        length ([] ++ xs)               ≅<>
        length xs                       ∎))
    ++-right-injective xs {[]} {z :: zs} eq = contradiction-implies-anything (nat-not-nonzero-plus-itself (length zs) (length xs) (begin≅
        suc (length zs) + length xs     ≅<>
        length (z :: zs) + length xs    ≅< symmetric-on ℕ (length-distributes-over-++ (z :: zs) xs) >
        length (z :: zs ++ xs)          ≅< symmetric-on ℕ (equal-implies-equal-lengths eq) >
        length ([] ++ xs)               ≅<>
        length xs                       ∎))
    ++-right-injective _ {[]} {[]} _ = []=[]
    ++-right-injective xs {_ :: _} {_ :: _} (cons=[]=cons eqyz eq) = cons=[]=cons eqyz (++-right-injective xs eq)

instance
    ++-bi-injective : BiInjective _++_
    ++-bi-injective = record {left-injective = ++-left-injective; right-injective = ++-right-injective}
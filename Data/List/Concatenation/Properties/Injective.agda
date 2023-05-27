open import Agda.Primitive
open import Structure.Setoid

module Data.List.Concatenation.Properties.Injective {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Data.List
open import Function.Unary.Properties
open import Data.List.Setoid A {{SA}}
open import Structure.Setoid.Equation
open import Function.Binary.Properties
open import Data.List.Concatenation.Properties A {{SA}}
open import Logic
open import Data.List.Length A {{SA}}
open import Data.Number.Nat
open import Data.Number.Nat.Base
open import Data.List.Properties A {{SA}}

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
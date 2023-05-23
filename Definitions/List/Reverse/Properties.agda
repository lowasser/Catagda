open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Reverse.Properties {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open Setoid {{...}}

open import Definitions.List
open import Definitions.List.Properties {ℓA} {ℓ=A} A
open import Definitions.List.Concatenation.Properties {ℓA} {ℓ=A} A
open import Definitions.List.Setoid {ℓA} {ℓ=A} A
open import Definitions.Setoid.Equation
open import Definitions.List.Reverse
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Isomorphism

private
    reverse-singleton : (x : A) → reverse [ x :] ≅ [ x :]
    reverse-singleton x = begin≅
        reverse [ x :]          ≅<>
        reverse [] ++ [ x :]    ≅<>
        [] ++ [ x :]            ≅<>
        [ x :]                  ∎

    reverse-congruent : Congruent reverse
    reverse-congruent []=[] = []=[]
    reverse-congruent {x :: xs} {y :: ys} (cons=[]=cons x≅y xs≅ys) = begin≅
        reverse (x :: xs)       ≅<>
        reverse xs ++ [ x :]    ≅< left-congruent-on _++_ (right-congruent-on _::_ x≅y) >
        reverse xs ++ [ y :]    ≅< right-congruent-on _++_ (reverse-congruent xs≅ys) >
        reverse ys ++ [ y :]    ≅<>
        reverse (y :: ys)       ∎

instance
    reverse-IsCongruent : IsCongruent reverse
    reverse-IsCongruent = record { congruent = reverse-congruent }

reverse-++ : (xs ys : [ A ]) → reverse (xs ++ ys) ≅ reverse ys ++ reverse xs
reverse-++ [] ys = begin≅
    reverse ([] ++ ys)          ≅<>
    reverse ys                  ≅< symmetric-on [ A ] (right-id-on _++_ (reverse ys)) >
    reverse ys ++ []            ≅<>
    reverse ys ++ reverse []    ∎
reverse-++ (x :: xs) ys = begin≅
    reverse ((x :: xs) ++ ys)               ≅<>
    reverse (x :: (xs ++ ys))               ≅<>
    reverse (xs ++ ys) ++ [ x :]            ≅< right-congruent-on _++_ (reverse-++ xs ys) >
    (reverse ys ++ reverse xs) ++ [ x :]    ≅< symmetric-on [ A ] (associate-on _++_ (reverse ys) (reverse xs) [ x :]) >
    reverse ys ++ (reverse xs ++ [ x :])    ≅<>
    reverse ys ++ reverse (x :: xs)         ∎

reverse-reverse : (xs : [ A ]) → reverse (reverse xs) ≅ xs
reverse-reverse [] = reflexive-on [ A ] []
reverse-reverse (x :: xs) = begin≅
    reverse (reverse (x :: xs))             ≅<>
    reverse (reverse xs ++ [ x :])          ≅< reverse-++ (reverse xs) [ x :] >
    reverse [ x :] ++ reverse (reverse xs)  ≅< right-congruent-on _++_ (reverse-singleton x) >
    [ x :] ++ reverse (reverse xs)          ≅< left-congruent-on _++_ (reverse-reverse xs) >
    [ x :] ++ xs                            ≅<>
    x :: xs                                 ∎

reverse-map-commute : {ℓB : Level} {B : Set ℓB} → (f : B → A) → (bs : [ B ]) → reverse (map f bs) ≅ map f (reverse bs)
reverse-map-commute _ [] = reflexive-on [ A ] []
reverse-map-commute f (x :: xs) = begin≅
    reverse (map f (x :: xs))           ≅<>
    reverse (f x :: map f xs)           ≅<>
    reverse (map f xs) ++ [ f x :]      ≅< right-congruent-on _++_ (reverse-map-commute f xs) >
    map f (reverse xs) ++ [ f x :]      ≅<>
    map f (reverse xs) ++ map f [ x :]  ≅< symmetric-on [ A ] (map-distributes-over-++ f (reverse xs) [ x :]) >
    map f (reverse xs ++ [ x :])        ≅<>
    map f (reverse (x :: xs))           ∎
open import Agda.Primitive
open import Structure.Setoid

module Data.List.Length {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Agda.Builtin.Unit
open import Data.List
open import Data.Number.Nat.Base renaming (_≅_ to _=N_)
open import Data.Number.Nat
open import Data.List.Setoid A {{SA}}
open import Relation.Equivalence.Structural.Properties ⊤ renaming (≡-setoid to ⊤-setoid)
open import Logic
open import Structure.Setoid.Equation
open import Data.List.Concatenation.Properties ⊤ {{⊤-setoid}}

open Setoid {{...}}

private
    const-tt : A → ⊤
    const-tt _ = tt

length : [ A ] → ℕ
length = map const-tt

equal-implies-equal-lengths : {xs ys : [ A ]} → xs =[]= ys → length xs =N length ys 
equal-implies-equal-lengths []=[] = reflexive-on ℕ 0ℕ
equal-implies-equal-lengths (cons=[]=cons _ xs=ys) = suc= (equal-implies-equal-lengths xs=ys)

length-distributes-over-++ : (xs ys : [ A ]) → length (xs ++ ys) =N length xs + length ys
length-distributes-over-++ = map-distributes-over-++ const-tt

list-not-nonempty-++-itself : (x : A) (xs ys : [ A ]) → ¬ (((x :: xs) ++ ys) =[]= ys)
list-not-nonempty-++-itself x xs ys eq = nat-not-nonzero-plus-itself (length xs) (length ys) (begin≅
    suc (length xs) + length ys     ≅<>
    length (x :: xs) + length ys    ≅< symmetric-on ℕ (length-distributes-over-++ (x :: xs) ys) >
    length ((x :: xs) ++ ys)        ≅< equal-implies-equal-lengths eq >
    length ys                       ∎)
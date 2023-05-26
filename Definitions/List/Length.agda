open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Length {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Agda.Builtin.Unit
open import Definitions.List
open import Definitions.Nat renaming (_≅_ to _=N_) hiding (_=[]=_)
open import Definitions.List.Setoid A {{SA}}
open import Definitions.Logic
open import Definitions.Setoid.Equation

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
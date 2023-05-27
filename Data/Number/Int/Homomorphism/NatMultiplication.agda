module Data.Number.Int.Homomorphism.NatMultiplication where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Structure.Category.Mon
open import Data.Number.Nat hiding (_≅_) renaming (_*_ to _*N_; *-monoid to ℕ*-monoid)
open import Data.List
open import Data.Number.Int.Base hiding (_≅_)
open import Data.Number.Int.Multiplication renaming (*-monoid to ℤ*-monoid)
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Ring
open import Function.Binary.Properties

open Setoid {{...}}
open Ring {{...}}

private
    ntoz-distributes-* : (a b : ℕ) → ℕ-to-ℤ (a *N b) ≅ ℕ-to-ℤ a * ℕ-to-ℤ b
    ntoz-distributes-* a b = z= (begin≅
        a *N b + (a *N 0ℕ + 0ℕ *N b)    ≅< left-congruent-on _+_ (right-congruent-on _+_ (Ring.right-zero *-+-ring a)) >
        {!   !}                          ≅< {!   !} >
        (a *N b + 0ℕ *N 0ℕ) + 0ℕ        ∎)
        where open Ring *-+-ring
{-
ℕ+-to-ℤ+ : MonHom (mon-ob ℕ*-monoid) (mon-ob ℤ*-monoid)
ℕ+-to-ℤ+ = record {
    function = ℕ-Congruent→-ℤ;
    identity-to-identity = reflexive-on ℤ 0ℤ;
    distributes = ntoz-distributes-+}-}
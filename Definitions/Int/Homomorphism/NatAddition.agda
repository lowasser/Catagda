module Definitions.Int.Homomorphism.NatAddition where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Definitions.Category.Mon
open import Definitions.Nat hiding (_≅_; _+_)
open import Definitions.List
open import Definitions.List.Concatenation.Properties {lzero} {lzero} ⊤ renaming (++-Monoid to ℕ+-monoid)
open import Definitions.Int.Base hiding (_≅_)
open import Definitions.Int.Addition renaming (+-monoid to ℤ+-monoid)
open import Definitions.Setoid
open import Definitions.Setoid.Equation

open Setoid {{...}}

private
    ntoz-distributes-+ : (a b : ℕ) → ℕ-to-ℤ (a ++ b) ≅ ℕ-to-ℤ a + ℕ-to-ℤ b
    ntoz-distributes-+ a b = z= (reflexive-on ℕ ((a ++ b) ++ (0ℕ ++ 0ℕ)))

ℕ+-to-ℤ+ : MonHom (mon-ob ℕ+-monoid) (mon-ob ℤ+-monoid)
ℕ+-to-ℤ+ = record {
    function = ℕ-Congruent→-ℤ;
    identity-to-identity = reflexive-on ℤ 0ℤ;
    distributes = ntoz-distributes-+}
module Definitions.Relation.Equivalence.Structural where

open import Agda.Primitive
open import Definitions.Relation

data _≡_ {ℓ : Level} { A : Set ℓ } : Relation A where
    refl : { x : A } → x ≡ x

infix 3 _≡_
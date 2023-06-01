module Predicate.Properties where

open import Agda.Primitive 
open import Predicate

private
    variable
        ℓA ℓP ℓQ : Level

record Iff {A : Set ℓA} (P : Predicate ℓP A) (Q : Predicate ℓQ A) : Set (ℓA ⊔ ℓP ⊔ ℓQ) where
    field
        implication→ : (a : A) → P a → Q a
        implication← : (a : A) → Q a → P a

    commute : Iff Q P
    commute = record {implication→ = implication←; implication← = implication→}
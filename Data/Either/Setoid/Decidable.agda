open import Agda.Primitive
open import Structure.Setoid.Decidable

module Data.Either.Setoid.Decidable {ℓA ℓ=A ℓB ℓ=B : Level} (A : Set ℓA) (B : Set ℓB) {{DSA : DecidableSetoid ℓ=A A}} {{SB : DecidableSetoid ℓ=B B}} where

open DecidableSetoid {{...}}

open import Structure.Setoid
open import Data.Either 
open import Relation.Properties
open import Data.Either.Setoid {ℓA} {ℓ=A} {ℓB} {ℓ=B} A B
open import Definitions.Not

open Setoid {{...}}
open Decidable {{...}}

private
    e=-decide-lr : (a : A) → (b : B) → ¬ (left a ≅ right b)
    e=-decide-lr _ _ ()

    e=-decide-rl : (a : B) → (b : A) → ¬ (right a ≅ left b)
    e=-decide-rl _ _ ()

    e=-decide-ll : {x y : A} → x ≇ y → left x ≇ left y
    e=-decide-ll x≇y (l= lxly) = x≇y lxly

    e=-decide-rr : {x y : B} → x ≇ y → right x ≇ right y
    e=-decide-rr x≇y (r= rxry) = x≇y rxry

    e=-decide : (x : Either A B) → (y : Either A B) → Either (x ≅ y) (¬ (x ≅ y))
    e=-decide (left x) (right y) = right (e=-decide-lr x y)
    e=-decide (right x) (left y) = right (e=-decide-rl x y)
    e=-decide (left x) (left y) with decide x y
    ... | left x≅y      = left (l= x≅y)
    ... | right x≇y     = right (e=-decide-ll x≇y)
    e=-decide (right x) (right y) with decide x y
    ... | left x≅y      = left (r= x≅y)
    ... | right x≇y     = right (e=-decide-rr x≇y)

instance
    e=-DecidableSetoid : DecidableSetoid (ℓ=A ⊔ ℓ=B) (Either A B)
    e=-DecidableSetoid = make-decidable-setoid e=-decide
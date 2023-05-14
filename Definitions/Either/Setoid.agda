open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Either.Setoid {ℓA ℓ=A ℓB ℓ=B : Level} (A : Set ℓA) (B : Set ℓB) {{SA : Setoid ℓ=A A}} {{SB : Setoid ℓ=B B}} where

open import Definitions.Either
open import Definitions.Relation
open import Definitions.Relation.Properties

open Setoid {{...}}
open Equivalence {{...}}
open PreOrder {{...}}
open IsSymmetric {{...}}
open IsReflexive {{...}}
open IsTransitive {{...}}

data _e=_ : Rel (ℓ=A ⊔ ℓ=B) (Either A B) where
    l= : {a1 a2 : A} → a1 ≅ a2 → left a1 e= left a2
    r= : {b1 b2 : B} → b1 ≅ b2 → right b1 e= right b2

private
    e=-reflexive : Reflexive _e=_
    e=-reflexive (left x) = l= (reflexive x)
    e=-reflexive (right y) = r= (reflexive y)

    e=-transitive : Transitive _e=_
    e=-transitive (l= x≅y) (l= y≅z) = l= (transitive x≅y y≅z)
    e=-transitive (r= x≅y) (r= y≅z) = r= (transitive x≅y y≅z)

    e=-symmetric : Symmetric _e=_
    e=-symmetric (l= x≅y) = l= (symmetric x≅y)
    e=-symmetric (r= x≅y) = r= (symmetric x≅y)

instance
    either-setoid : Setoid (ℓ=A ⊔ ℓ=B) (Either A B)
    either-setoid = make-setoid _e=_ e=-reflexive e=-transitive e=-symmetric

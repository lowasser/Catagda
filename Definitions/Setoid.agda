open import Agda.Primitive

module Definitions.Setoid where

open import Definitions.Not
open import Definitions.Relation
open import Definitions.Relation.Properties

open Equivalence {{...}}
open PreOrder {{...}}
open IsTransitive {{...}}
open IsSymmetric {{...}}

record Setoid {ℓA : Level} (ℓ= : Level) (A : Set ℓA) : Set (ℓA ⊔ lsuc ℓ=) where
    field
        _≅_ : Rel ℓ= A
        {{equivalence}} : Equivalence _≅_
        
    infix 4 _≅_

    _≇_ : Rel ℓ= A
    a ≇ b = ¬ (a ≅ b)

make-setoid : {ℓA ℓ=A : Level} {A : Set ℓA} → (_≅_ : Rel ℓ=A A) → Reflexive _≅_ → Transitive _≅_ → Symmetric _≅_ → Setoid ℓ=A A
make-setoid _≅_ refl trans sym = record { _≅_ = _≅_ ; equivalence = make-equivalence _≅_ refl trans sym}

≅-on : {ℓB ℓ=B : Level} → (B : Set ℓB) → {{SB : Setoid ℓ=B B}} → Rel ℓ=B B
≅-on _ {{SB}} = Setoid._≅_ SB

reflexive-on : {ℓB ℓ=B : Level} → (B : Set ℓB) → {{SB : Setoid ℓ=B B}} → Reflexive (≅-on B)
reflexive-on _ {{SB}} = IsReflexive.reflexive (PreOrder.is-reflexive (Equivalence.preorder (Setoid.equivalence SB)))

symmetric-on : {ℓB ℓ=B : Level} → (B : Set ℓB) → {{SB : Setoid ℓ=B B}} → Symmetric (≅-on B)
symmetric-on _ {{SB}} = IsSymmetric.symmetric (Equivalence.is-symmetric (Setoid.equivalence SB))

transitive-on : {ℓB ℓ=B : Level} → (B : Set ℓB) → {{SB : Setoid ℓ=B B}} → Transitive (≅-on B)
transitive-on _ {{SB}} = IsTransitive.transitive (PreOrder.is-transitive (Equivalence.preorder (Setoid.equivalence SB)))
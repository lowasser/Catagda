open import Agda.Primitive

module Definitions.Relation.Equivalence.Structural.Properties {ℓ : Level} (A : Set ℓ) where

open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation
open import Definitions.Relation.Properties 
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid

private
    _≅_ : Rel ℓ A
    _≅_ = _≡_ {ℓ} {A}

private
    ≡-reflexive : Reflexive _≅_
    ≡-reflexive _ = refl

    ≡-symmetric : Symmetric _≅_
    ≡-symmetric refl = refl

    ≡-transitive : Transitive _≅_
    ≡-transitive refl refl = refl

instance
    ≡-is-reflexive : IsReflexive _≅_
    ≡-is-reflexive = record { reflexive = ≡-reflexive }

    ≡-is-transitive : IsTransitive _≅_
    ≡-is-transitive = record { transitive = ≡-transitive }

    ≡-is-preorder : PreOrder _≅_
    ≡-is-preorder = record {}

    ≡-is-symmetric : IsSymmetric _≅_
    ≡-is-symmetric = record { symmetric = ≡-symmetric }

    ≡-Equivalence : Equivalence _≅_
    ≡-Equivalence = record {}

open Equivalence{{...}}
open IsReflexive{{...}}

instance
    ≡-Setoid : Setoid ℓ A
    ≡-Setoid = record {_≅_ = _≡_ }

private
    variable
        ℓB ℓ=B : Level

≡-congruent : {B : Set ℓB} → {{SB : Setoid ℓ=B B}} → (f : A → B) → Congruent f
≡-congruent f {a1} refl = reflexive (f a1)

private
    ≡-left-congruent : {B : Set ℓB} → {{SB : Setoid ℓ=B B}} → (f : A → A → B) → LeftCongruent f
    ≡-left-congruent f {a} {b} refl = reflexive (f a b)

    ≡-right-congruent : {B : Set ℓB} → {{SB : Setoid ℓ=B B}} → (f : A → A → B) → RightCongruent f
    ≡-right-congruent f {b} {a} refl = reflexive (f a b)

≡-bi-congruent : {B : Set ℓB} → {{SB : Setoid ℓ=B B}} → (f : A → A → B) → BiCongruent f
≡-bi-congruent f = record {left-congruent = ≡-left-congruent f ; right-congruent = ≡-right-congruent f}
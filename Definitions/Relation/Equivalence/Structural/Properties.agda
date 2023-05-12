open import Agda.Primitive

module Definitions.Relation.Equivalence.Structural.Properties {ℓ : Level} (A : Set ℓ) where

open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence
open import Definitions.Relation
open import Definitions.Relation.Properties 
open import Definitions.Relation.Order.Pre
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid

private
    ≡-reflexive : Reflexive {ℓ} {A} _≡_
    ≡-reflexive _ = refl

    ≡-symmetric : Symmetric {ℓ} {A} _≡_
    ≡-symmetric refl = refl

    ≡-transitive : Transitive {ℓ} {A} _≡_
    ≡-transitive refl refl = refl

instance
    ≡-is-reflexive : IsReflexive {ℓ} {A} _≡_
    ≡-is-reflexive = record { reflexive = ≡-reflexive }

    ≡-is-transitive : IsTransitive {ℓ} {A} _≡_
    ≡-is-transitive = record { transitive = ≡-transitive }

    ≡-is-preorder : PreOrder {ℓ} {A} _≡_
    ≡-is-preorder = record {}

    ≡-is-symmetric : IsSymmetric {ℓ} {A} _≡_
    ≡-is-symmetric = record { symmetric = ≡-symmetric }

    ≡-Equivalence : Equivalence {ℓ} {A} _≡_
    ≡-Equivalence = record {}

open Equivalence{{...}}
open IsReflexive{{...}}

instance
    ≡-Setoid : Setoid A
    ≡-Setoid = record {_≈_ = _≡_ }

≡-congruent : {ℓB : Level} {B : Set ℓB} → {{SB : Setoid B}} → (f : A → B) → Congruent f
≡-congruent f {a1} refl = reflexive (f a1)

private
    ≡-left-congruent : {ℓB : Level} {B : Set ℓB} → {{SB : Setoid B}} → (f : A → A → B) → LeftCongruent f
    ≡-left-congruent f {a} {b} refl = reflexive (f a b)

    ≡-right-congruent : {ℓB : Level} {B : Set ℓB} → {{SB : Setoid B}} → (f : A → A → B) → RightCongruent f
    ≡-right-congruent f {b} {a} refl = reflexive (f a b)

≡-bi-congruent : {ℓB : Level} {B : Set ℓB} → {{SB : Setoid B}} → (f : A → A → B) → BiCongruent f
≡-bi-congruent f = record {left-congruent = ≡-left-congruent f ; right-congruent = ≡-right-congruent f}
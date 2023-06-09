module Relation.Order.Total where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Either
open import Structure.Setoid
open import Relation
open import Relation.Properties
open import Relation.Order.Partial
open import Logic

open IsReflexive {{...}}

private
    variable
        ℓA ℓB ℓC ℓ=A ℓ≤A : Level

data Tri {A : Set ℓA} (_~_ : Rel ℓB A) (_≺_ : Rel ℓC A) : A → A → Set (ℓB ⊔ ℓC) where
    triL : {x y : A} → x ≺ y → ¬ (x ~ y) → ¬ (y ≺ x) → Tri _~_ _≺_ x y
    triE : {x y : A} → x ~ y → Tri _~_ _≺_ x y
    triG : {x y : A} → ¬ (x ≺ y) → ¬ (x ~ y) → y ≺ x → Tri _~_ _≺_ x y

data Ordering : Set where
    less-than : Ordering
    equal-to : Ordering
    greater-than : Ordering

open import Relation.Equivalence.Structural.Properties Ordering

tri-to-ordering : {A : Set ℓA} {_~_ : Rel ℓB A} {_≺_ : Rel ℓC A} {a b : A} → Tri _~_ _≺_ a b → Ordering
tri-to-ordering (triL _ _ _) = less-than
tri-to-ordering (triE _) = equal-to
tri-to-ordering (triG _ _ _) = greater-than

record TotalOrder {A : Set ℓA} {{AS : Setoid ℓ=A A}} (_≤_ : Rel ℓ≤A A) : Set (ℓA ⊔ ℓ=A ⊔ ℓ≤A) where
    field
        {{is-partial-order}} : PartialOrder _≤_

    open Setoid {{...}}
    open PartialOrder is-partial-order
    
    field
        trichotomy : (a b : A) → Tri _≅_ _≤_ a b

    compare : (a b : A) → Either (a ≤ b) (b ≤ a)
    compare a b with trichotomy a b
    ... | triL lt _ _ = left lt
    ... | triE eq = left (reflexive-equiv eq)
    ... | triG _ _ gt = right gt

    order : (a b : A) → Ordering
    order a b = tri-to-ordering (trichotomy a b)

open TotalOrder {{...}}

trichotomy-on : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{TO : TotalOrder _≤_}} → (a b : A) → Tri (Setoid._≅_ AS) _≤_ a b
trichotomy-on _≤_ {{TO}} = TotalOrder.trichotomy TO

compare-order-on : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{TO : TotalOrder _≤_}} → (a b : A) → Either (a ≤ b) (b ≤ a)
compare-order-on _ = compare
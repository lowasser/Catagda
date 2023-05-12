module Definitions.Setoid.Equation where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Relation.Equivalence
open import Definitions.Relation
open import Definitions.Relation.Properties

open Setoid {{...}}
open Equivalence {{...}}
open IsReflexive {{...}}
open IsTransitive {{...}}

begin≈_ : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → {x y : A} → x ≈ y → x ≈ y
begin≈_ p = p

_∎ : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (x : A) → x ≈ x
x ∎ = reflexive x

_≈<_>_ : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (x : A) → { y z : A } → x ≈ y → y ≈ z → x ≈ z
x ≈< p > q = transitive p q

_≈<>_ : {ℓ : Level} {A : Set ℓ} → {{SA : Setoid A}} → (x : A) → { y : A } → x ≈ y → x ≈ y
x ≈<> q = x ≈< reflexive x > q

infix 1 begin≈_
infix 3 _∎
infixr 2 _≈<_>_
infixr 2 _≈<>_
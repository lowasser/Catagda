module Definitions.Setoid.Equation where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Equivalence.Structural

open Setoid {{...}}
open Equivalence {{...}}
open IsReflexive {{...}}
open IsTransitive {{...}}
open IsSymmetric {{...}}

private
    variable
        ℓA ℓ=A : Level
        A : Set ℓA

begin≅_ : {{SA : Setoid ℓ=A A}} → {x y : A} → x ≅ y → x ≅ y
begin≅_ p = p

_∎ : {{SA : Setoid ℓ=A A}} → (x : A) → x ≅ x
x ∎ = reflexive x

_≅<_>_ : {{SA : Setoid ℓ=A A}} → (x : A) → { y z : A } → x ≅ y → y ≅ z → x ≅ z
x ≅< p > q = transitive p q

_≡<_>_ : {{SA : Setoid ℓ=A A}} → (x : A) → { y z : A } → x ≡ y → y ≅ z → x ≅ z
x ≡< refl > q = q

_≅<>_ : {{SA : Setoid ℓ=A A}} → (x : A) → { y : A } → x ≅ y → x ≅ y
x ≅<> q = x ≅< reflexive x > q

infix 1 begin≅_
infix 3 _∎
infixr 2 _≅<_>_
infixr 2 _≡<_>_
infixr 2 _≅<>_

≇-left-≅ : {{SA : Setoid ℓ=A A}} → {a b c : A} → a ≅ b → b ≇ c → a ≇ c
≇-left-≅ {_} {_} {_} {a} {b} {c} a≅b b≇c a≅c = b≇c (begin≅
    b       ≅< symmetric a≅b >
    a       ≅< a≅c >
    c       ∎)

≇-right-≅ : {{SA : Setoid ℓ=A A}} → {a b c : A} → a ≇ b → b ≅ c → a ≇ c
≇-right-≅ {_} {_} {_} {a} {b} {c} a≇b b≅c a≅c = a≇b (begin≅
    a       ≅< a≅c >
    c       ≅< symmetric (b≅c) >
    b       ∎)

≇-symmetric : {{SA : Setoid ℓ=A A}} → {a b : A} → a ≇ b → b ≇ a
≇-symmetric {_} {_} {_} {a} {b} a≇b b≅a = a≇b (symmetric b≅a)
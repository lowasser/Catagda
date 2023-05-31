module Relation.Equivalence.Structural where

open import Agda.Primitive
open import Relation

data _≡_ {ℓ : Level} { A : Set ℓ } : Relation A where
    refl : { x : A } → x ≡ x

infix 3 _≡_

≡-cong : {ℓA ℓB : Level} {A : Set ℓA} {B : Set ℓB} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
≡-cong _ refl = refl

≡-sym : {ℓA : Level} {A : Set ℓA} {x y : A} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {ℓA : Level} {A : Set ℓA} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl
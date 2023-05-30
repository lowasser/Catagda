module Relation.Order.Partial where

open import Agda.Primitive
open import Structure.Setoid
open import Relation
open import Relation.Properties
open import Function.Binary.Properties
open import Logic
open import Agda.Builtin.Sigma

open Setoid {{...}}

private
    variable
        ℓA ℓ=A ℓ≤A : Level

Antisymmetric : { A : Set ℓA } → {{AS : Setoid ℓ=A A}} → Rel ℓ≤A A → Set (ℓA ⊔ ℓ=A ⊔ ℓ≤A)
Antisymmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x → x ≅ y

record IsAntisymmetric { A : Set ℓA } {{AS : Setoid ℓ=A A}} (_≤_ : Rel ℓ≤A A) : Set (ℓA ⊔ ℓ=A ⊔ ℓ≤A) where
    field
        antisymmetric : Antisymmetric _≤_

record PartialOrder {A : Set ℓA} {{AS : Setoid ℓ=A A}} (_≤_ : Rel ℓ≤A A) : Set (ℓA ⊔ ℓ=A ⊔ ℓ≤A) where
    field
        {{is-preorder}} : PreOrder _≤_
        {{is-antisymmetric}} : IsAntisymmetric _≤_
        reflexive-equiv : {a b : A} → a ≅ b → a ≤ b

    left-congruent-law : {a1 a2 b : A} → a1 ≅ a2 → a1 ≤ b → a2 ≤ b
    left-congruent-law a1=a2 a1≤b = IsTransitive.transitive (PreOrder.is-transitive is-preorder) (reflexive-equiv (symmetric-on A a1=a2)) a1≤b

    right-congruent-law : {a b1 b2 : A} → b1 ≅ b2 → a ≤ b1 → a ≤ b2
    right-congruent-law b1=b2 a≤b1 = IsTransitive.transitive (PreOrder.is-transitive is-preorder) a≤b1 (reflexive-equiv b1=b2)

open IsReflexive {{...}}
open IsTransitive {{...}}
open IsAntisymmetric {{...}}
open PartialOrder {{...}}

reflexive-order-on : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → Reflexive _≤_
reflexive-order-on _ = reflexive

reflexive-equiv-order-on : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → {a b : A} → a ≅ b → a ≤ b
reflexive-equiv-order-on _ = reflexive-equiv

transitive-order-on : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → Transitive _≤_
transitive-order-on _ = transitive

antisymmetric-order-on : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → Antisymmetric _≤_
antisymmetric-order-on _ = antisymmetric

right-congruent-on-order : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → {a1 a2 b : A} → a1 ≅ a2 → a1 ≤ b → a2 ≤ b
right-congruent-on-order _ = left-congruent-law

left-congruent-on-order : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → {a b1 b2 : A} → b1 ≅ b2 → a ≤ b1 → a ≤ b2
left-congruent-on-order _ = right-congruent-law

bi-congruent-order : {A : Set ℓA} → {{AS : Setoid ℓ=A A}} → (_≤_ : Rel ℓ≤A A) → {{PO : PartialOrder _≤_}} → {a1 a2 b1 b2 : A} → a1 ≅ a2 → b1 ≅ b2 → a2 ≤ b2 → a1 ≤ b1
bi-congruent-order {_} {_} {_} {A} _≤_ a1=a2 b1=b2 a2≤b2 = right-congruent-on-order _≤_ (symmetric-on A a1=a2) (left-congruent-on-order _≤_ (symmetric-on A b1=b2) a2≤b2)
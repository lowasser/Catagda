module Definitions.Relation.Order.Partial where

open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Relation.Order.Pre

open Setoid {{...}}

Antisymmetric : { ℓ : Level } { A : Set ℓ } → {{AS : Setoid A}} → Relation A → Set ℓ
Antisymmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x → x ≅ y

record IsAntisymmetric  { ℓ : Level } { A : Set ℓ } {{AS : Setoid A}} (_≤_ : Relation A) : Set ℓ where
    field
        antisymmetric : Antisymmetric _≤_

record PartialOrder {ℓ : Level} {A : Set ℓ} {{AS : Setoid A}} (_≤_ : Relation A) : Set ℓ where
    field
        {{is-preorder}} : PreOrder _≤_
        {{is-antisymmetric}} : IsAntisymmetric _≤_
        left-congruent-law : {a1 a2 b : A} → a1 ≅ a2 → a1 ≤ b → a2 ≤ b
        right-congruent-law : {a b1 b2 : A} → b1 ≅ b2 → a ≤ b1 → a ≤ b2

open IsReflexive {{...}}
open IsTransitive {{...}}
open IsAntisymmetric {{...}}

reflexive-order-on : {ℓ : Level} {A : Set ℓ} → {{AS : Setoid A}} → (_≤_ : Relation A) → {{PO : PartialOrder _≤_}} → Reflexive _≤_
reflexive-order-on _ = reflexive

transitive-order-on : {ℓ : Level} {A : Set ℓ} → {{AS : Setoid A}} → (_≤_ : Relation A) → {{PO : PartialOrder _≤_}} → Transitive _≤_
transitive-order-on _ = transitive

antisymmetric-order-on : {ℓ : Level} {A : Set ℓ} → {{AS : Setoid A}} → (_≤_ : Relation A) → {{PO : PartialOrder _≤_}} → Antisymmetric _≤_
antisymmetric-order-on _ = antisymmetric
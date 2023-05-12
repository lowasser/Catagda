module Definitions.Relation.Properties where

open import Agda.Primitive
open import Definitions.Relation
open import Definitions.Either

Reflexive : { ℓ : Level } { A : Set ℓ } → Relation A → Set ℓ
Reflexive _∼_ = ∀ x → x ∼ x

record IsReflexive { ℓ : Level } { A : Set ℓ } (_∼_ : Relation A) : Set ℓ where
    field
        reflexive : Reflexive _∼_

Symmetric : { ℓ : Level } { A : Set ℓ } → Relation A → Set ℓ
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x

record IsSymmetric { ℓ : Level } { A : Set ℓ } (_∼_ : Relation A) : Set ℓ where
    field
        symmetric : Symmetric _∼_

Transitive : { ℓ : Level } { A : Set ℓ } → Relation A → Set ℓ
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

record IsTransitive  { ℓ : Level } { A : Set ℓ } (_∼_ : Relation A) : Set ℓ where
    field
        transitive : Transitive _∼_
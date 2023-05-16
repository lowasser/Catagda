module Definitions.Relation.Properties where

open import Agda.Primitive
open import Definitions.Either
open import Definitions.Logic
open import Definitions.Relation

private variable
    ℓA ℓB ℓ=A ℓ=AB : Level

Reflexive : { A : Set ℓA } → Rel ℓB A → Set (ℓA ⊔ ℓB)
Reflexive _∼_ = ∀ x → x ∼ x

record IsReflexive { A : Set ℓA } (_∼_ : Rel ℓ=A A) : Set (ℓA ⊔ ℓ=A) where
    field
        reflexive : Reflexive _∼_

Antireflexive : { A : Set ℓA } → Rel ℓB A → Set (ℓA ⊔ ℓB)
Antireflexive _≁_ = ∀ x → ¬ (x ≁ x)

record IsAntireflexive { A : Set ℓA } (_≁_ : Rel ℓ=A A) : Set (ℓA ⊔ ℓ=A) where
    field
        antireflexive : Antireflexive _≁_

Symmetric : { A : Set ℓA } → Rel ℓB A → Set (ℓA ⊔ ℓB)
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x

record IsSymmetric { A : Set ℓA } (_∼_ : Rel ℓ=A A) : Set (ℓA ⊔ ℓ=A) where
    field
        symmetric : Symmetric _∼_

Transitive : { A : Set ℓA } → Rel ℓ=A A → Set (ℓA ⊔ ℓ=A)
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

record IsTransitive { A : Set ℓA } (_∼_ : Rel ℓ=A A) : Set (ℓA ⊔ ℓ=A) where
    field
        transitive : Transitive _∼_

record PreOrder {A : Set ℓA} (_~_ : Rel ℓ=A A) : Set (ℓA ⊔ ℓ=A) where
    field
        {{is-reflexive}} : IsReflexive _~_
        {{is-transitive}} : IsTransitive _~_

make-preorder : {A : Set ℓA} → (_~_ : Rel ℓ=A A) → Reflexive _~_ → Transitive _~_ → PreOrder _~_
make-preorder _ refl trans = record {is-reflexive = record {reflexive = refl}; is-transitive = record {transitive = trans}}

record Equivalence { A : Set ℓA } (_∼_ : Rel ℓ=A A) : Set (ℓA ⊔ ℓ=A) where
    field
        {{preorder}} : PreOrder _∼_
        {{is-symmetric}} : IsSymmetric _∼_

make-equivalence : {A : Set ℓA} → (_~_ : Rel ℓ=A A) → Reflexive _~_ → Transitive _~_ → Symmetric _~_ → Equivalence _~_
make-equivalence _~_ refl trans sym = record {preorder = make-preorder _~_ refl trans; is-symmetric = record {symmetric = sym}}

record Decidable { A : Set ℓA } { B : Set ℓB } (_~_ : A → B → Set ℓ=AB) : Set (ℓA ⊔ ℓB ⊔ ℓ=AB) where
    field
        decide : (a : A) → (b : B) → Either (a ~ b) (¬ (a ~ b))
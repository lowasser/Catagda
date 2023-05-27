module Relation where

open import Agda.Primitive

Rel : {ℓA : Level} → (ℓB : Level) → (A : Set ℓA) → Set (ℓA ⊔ lsuc ℓB)
Rel ℓB A = A → A → Set ℓB

Relation : {ℓ : Level} → (A : Set ℓ) → Set (lsuc ℓ)
Relation {ℓ} = Rel ℓ

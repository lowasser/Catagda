open import Agda.Primitive

module Structure.Category.Set (ℓ : Level) where

open import Structure.Setoid
open import Structure.Category

record SetOb : Set (lsuc ℓ) where
    field
        elements : Set ℓ
        {{setoid}} : Setoid ℓ elements

record _⟶_ (A B : SetOb) : Set (lsuc ℓ) where

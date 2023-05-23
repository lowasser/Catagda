open import Agda.Primitive

module Definitions.Category.Set (ℓ : Level) where

open import Definitions.Setoid
open import Definitions.Category

record SetOb : Set (lsuc ℓ) where
    field
        elements : Set ℓ
        {{setoid}} : Setoid ℓ elements

record _⟶_ (A B : SetOb) : Set (lsuc ℓ) where

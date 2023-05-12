module Definitions.Category where

open import Agda.Primitive
open import Definitions.Function.Binary
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Equivalence
open import Definitions.Setoid

open Setoid {{...}}

record Category {ℓOb ℓ→ : Level} (Ob : Set ℓOb) {{SOB : Setoid Ob}} (_⟶_ : Ob → Ob → Set ℓ→) : Set (ℓOb ⊔ lsuc ℓ→) where
    field
        _∘_ : { a b c : Ob } → (b ⟶ c) → (a ⟶ b) → (a ⟶ c)
        left-congruent-arrow : { a1 a2 b : Ob } → a1 ≈ a2 → (a1 ⟶ b) → (a2 ⟶ b)
        right-congruent-arrow : { a b1 b2 : Ob } → (b1 ≈ b2) → (a ⟶ b1) → (a ⟶ b2)

        -- should probably express some isomorphisms about it?

        _=→_ : {a b : Ob} → Relation (a ⟶ b)
        =→-equivalence : {a b : Ob} → Equivalence (_=→_ {a} {b})
        =→-left-congruence : {a1 a2 b : Ob} → (a1≈a2 : a1 ≈ a2) → {ab1 ab2 : a1 ⟶ b} → ab1 =→ ab2 →
            (left-congruent-arrow a1≈a2 ab1) =→ (left-congruent-arrow a1≈a2 ab2)
        =→-right-congruence : {a b1 b2 : Ob} → (b1≈b2 : b1 ≈ b2) → {ab1 ab2 : a ⟶ b1} → ab1 =→ ab2 →
            (right-congruent-arrow b1≈b2 ab1) =→ (right-congruent-arrow b1≈b2 ab2)

        identity-arrow : (a : Ob) → a ⟶ a
        left-identity-law : {a b : Ob} → (f : a ⟶ b) → (identity-arrow b ∘ f) =→ f
        right-identity-law : {a b : Ob} → (f : a ⟶ b) → (f ∘ identity-arrow a) =→ f

        associative-law : {a b c d : Ob} → (h : c ⟶ d) → (g : b ⟶ c) → (f : a ⟶ b) → (h ∘ (g ∘ f)) =→ ((h ∘ g) ∘ f)
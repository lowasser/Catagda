module Structure.Category where

open import Agda.Primitive
open import Function.Binary
open import Relation
open import Relation.Properties
open import Structure.Setoid

open Setoid {{...}}

record Category {ℓOb ℓ=Ob ℓ→ ℓ=Arrow : Level} (Ob : Set ℓOb) {{SOB : Setoid ℓ=Ob Ob}} (_⟶_ : Ob → Ob → Set ℓ→) : Set (ℓOb ⊔ ℓ=Ob ⊔ lsuc ℓ=Arrow ⊔ lsuc ℓ→) where
    field
        _∘_ : { a b c : Ob } → (b ⟶ c) → (a ⟶ b) → (a ⟶ c)
        left-congruent-arrow : { a1 a2 b : Ob } → a1 ≅ a2 → (a1 ⟶ b) → (a2 ⟶ b)
        right-congruent-arrow : { a b1 b2 : Ob } → (b1 ≅ b2) → (a ⟶ b1) → (a ⟶ b2)

        -- should probably express some isomorphisms about it?

        _=Arrow_ : {a b : Ob} → Rel ℓ=Arrow (a ⟶ b)
        =Arrow-equivalence : {a b : Ob} → Equivalence (_=Arrow_ {a} {b})
        right-congruent-compose : { a b c : Ob } → {bc1 bc2 : b ⟶ c} → bc1 =Arrow bc2 → (ab : a ⟶ b) → (bc1 ∘ ab) =Arrow (bc2 ∘ ab)
        left-congruent-compose : { a b c : Ob } → {ab1 ab2 : a ⟶ b} → ab1 =Arrow ab2 → (bc : b ⟶ c) → (bc ∘ ab1) =Arrow (bc ∘ ab2)
        
        =Arrow-left-congruence : {a1 a2 b : Ob} → (a1≅a2 : a1 ≅ a2) → {ab1 ab2 : a1 ⟶ b} → ab1 =Arrow ab2 →
            (left-congruent-arrow a1≅a2 ab1) =Arrow (left-congruent-arrow a1≅a2 ab2)
        =Arrow-right-congruence : {a b1 b2 : Ob} → (b1≅b2 : b1 ≅ b2) → {ab1 ab2 : a ⟶ b1} → ab1 =Arrow ab2 →
            (right-congruent-arrow b1≅b2 ab1) =Arrow (right-congruent-arrow b1≅b2 ab2)

        identity-arrow : (a : Ob) → a ⟶ a
        left-identity-law : {a b : Ob} → (f : a ⟶ b) → (identity-arrow b ∘ f) =Arrow f
        right-identity-law : {a b : Ob} → (f : a ⟶ b) → (f ∘ identity-arrow a) =Arrow f

        associative-law : {a b c d : Ob} → (h : c ⟶ d) → (g : b ⟶ c) → (f : a ⟶ b) → (h ∘ (g ∘ f)) =Arrow ((h ∘ g) ∘ f)
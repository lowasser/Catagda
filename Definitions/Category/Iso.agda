module Definitions.Category.Iso where

open import Agda.Primitive 
open import Definitions.Setoid
open import Definitions.Category
open import Definitions.Setoid.Equation

private
    variable 
        ℓOb ℓ=Ob ℓArr ℓ=Arr : Level

record Inverses {Ob : Set ℓOb} {{OS : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓArr} (C : Category {ℓOb} {ℓ=Ob} {ℓArr} {ℓ=Arr} Ob _⟶_) {a b : Ob} (f : a ⟶ b) (g : b ⟶ a) : Set ℓ=Arr where
    open Category C
    field
        pre-compose : (f ∘ g) =Arrow identity-arrow b
        post-compose : (g ∘ f) =Arrow identity-arrow a

-- open Category
open Inverses

inverses-unique : {Ob : Set ℓOb} {{OS : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓArr} {C : Category {ℓOb} {ℓ=Ob} {ℓArr} {ℓ=Arr} Ob _⟶_} {a b : Ob} {f : a ⟶ b} {g h : b ⟶ a} 
    → Inverses C f g → Inverses C f h → Category._=Arrow_ C g h
inverses-unique {_} {_} {_} {ℓ=Arr} {_} {_⟶_} {C} {a} {b} {f} {g} {h} invfg invfh = begin≅
        g                       ≅< symmetric-on (b ⟶ a) (left-identity-law g) >
        identity-arrow a ∘ g    ≅< right-congruent-compose (symmetric-on (a ⟶ a) (post-compose invfh)) g >
        (h ∘ f) ∘ g             ≅< symmetric-on (b ⟶ a) (associative-law h f g) >
        h ∘ (f ∘ g)             ≅< left-congruent-compose (pre-compose invfg) h >
        h ∘ identity-arrow b    ≅< right-identity-law h >
        h                       ∎
    where   open Category C
            instance
                arr-setoid : Setoid ℓ=Arr (b ⟶ a)
                arr-setoid = record { _≅_ = Category._=Arrow_ C ; equivalence = Category.=Arrow-equivalence C} 
                back-arr-setoid : Setoid ℓ=Arr (a ⟶ a)
                back-arr-setoid = record { _≅_ = Category._=Arrow_ C ; equivalence = Category.=Arrow-equivalence C} 

data Isomorphic {Ob : Set ℓOb} {{OS : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓArr} (C : Category {ℓOb} {ℓ=Ob} {ℓArr} {ℓ=Arr} Ob _⟶_) (a b : Ob) : Set (ℓArr ⊔ ℓ=Arr) where
    iso : {f : a ⟶ b} {g : b ⟶ a} → Inverses C f g → Isomorphic C a b
module Definitions.Category.Commuting where

open import Agda.Primitive
open import Definitions.Category 
open import Definitions.Setoid 

private
    variable
        ℓOb ℓ=Ob ℓ→ ℓ=Arrow : Level

open Category {{...}}

data Path {Ob : Set ℓOb} {{SOB : Setoid ℓ=Ob Ob}} (_⟶_ : Ob → Ob → Set ℓ→) {{C : Category {ℓOb} {ℓ=Ob} {ℓ→} {ℓ=Arrow} Ob _⟶_}} : Ob → Ob → Set (ℓOb ⊔ ℓ→) where
    path-start : (a : Ob) → Path _⟶_ a a
    _path-snoc_ : {a b c : Ob} → Path _⟶_ b c → a ⟶ b → Path _⟶_ a c

_∘path_ : {Ob : Set ℓOb} {{SOB : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓ→} {{C : Category {ℓOb} {ℓ=Ob} {ℓ→} {ℓ=Arrow} Ob _⟶_}} → {a b c : Ob} → Path _⟶_ b c → Path _⟶_ a b → Path _⟶_ a c
p ∘path path-start _ = p
p ∘path (b⟶c path-snoc a→b) = (p ∘path b⟶c) path-snoc a→b

path-single : {Ob : Set ℓOb} {{SOB : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓ→} → {{C : Category {ℓOb} {ℓ=Ob} {ℓ→} {ℓ=Arrow} Ob _⟶_}} → {a b : Ob} → a ⟶ b → Path _⟶_ a b 
path-single {_} {_} {_} {_} {_} {_} {a} {b} arr = path-start b path-snoc arr

path-compose : {Ob : Set ℓOb} {{SOB : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓ→} → {{C : Category {ℓOb} {ℓ=Ob} {ℓ→} {ℓ=Arrow} Ob _⟶_}} → {a b : Ob} → Path _⟶_ a b → a ⟶ b
path-compose (path-start a) = identity-arrow a
path-compose (b⟶c path-snoc a→b) = (path-compose b⟶c) ∘ a→b

paths-commute : {Ob : Set ℓOb} {{SOB : Setoid ℓ=Ob Ob}} {_⟶_ : Ob → Ob → Set ℓ→} {{C : Category {ℓOb} {ℓ=Ob} {ℓ→} {ℓ=Arrow} Ob _⟶_}} {a b : Ob} → Path _⟶_ a b → Path _⟶_ a b → Set ℓ=Arrow
paths-commute pab1 pab2 = path-compose pab1 =Arrow path-compose pab2
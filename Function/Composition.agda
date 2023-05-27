module Function.Composition where

open import Agda.Primitive

_∘_ : {ℓA ℓB ℓC : Level} { A : Set ℓA } {B : Set ℓB} {C : Set ℓC} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
module Function.Endomorphism where

open import Agda.Primitive
open import Function.Composition renaming (_∘_ to _⊚_)
open import Function.Binary
open import Function renaming (id to idfn)

data Endo {ℓ : Level} (A : Set ℓ) : Set ℓ where
    endo : (A → A) → Endo A

_∘_ : {ℓ : Level} {A : Set ℓ} → BinOp (Endo A)
endo f ∘ endo g = endo (f ⊚ g)


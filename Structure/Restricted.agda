module Structure.Restricted where

open import Agda.Primitive

private
    variable
        ℓA ℓP : Level

data _RestrictedTo_ (A : Set ℓA) (P : A → Set ℓP) : Set (ℓA ⊔ ℓP) where 
    _constraint_ : (a : A) → P a → A RestrictedTo P

infix 5 _constraint_

-- equivalent to Σ but given a separate name
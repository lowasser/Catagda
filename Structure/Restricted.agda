module Structure.Restricted where

open import Agda.Primitive
open import Predicate

private
    variable
        ℓA ℓP : Level

data _RestrictedTo_ (A : Set ℓA) (P : Predicate ℓP A) : Set (ℓA ⊔ ℓP) where 
    _constraint_ : (a : A) → P a → A RestrictedTo P

infix 5 _constraint_

unrestricted : {A : Set ℓA} {P : Predicate ℓP A} → A RestrictedTo P → A
unrestricted (a constraint _) = a

-- equivalent to Σ but given a separate name
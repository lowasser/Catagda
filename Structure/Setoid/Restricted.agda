open import Agda.Primitive
open import Structure.Setoid

module Structure.Setoid.Restricted
    {ℓA ℓ=A ℓP : Level}
    (A : Set ℓA)
    {{SA : Setoid ℓ=A A}}
    (P : A → Set ℓP)
    where

open import Relation
open import Relation.Properties
open import Structure.Restricted
open Setoid {{...}}

data Restricted= : (Q : A → Set ℓP) → Rel ℓ=A (A RestrictedTo Q) where
    eq-restricted : {a b : A} → a ≅ b → {pa : P a} {pb : P b} → Restricted= P (a constraint pa) (b constraint pb)

instance
    restricted-setoid : Setoid ℓ=A (A RestrictedTo P)
    restricted-setoid = make-setoid (Restricted= P) reflexive transitive symmetric where
        reflexive : Reflexive (Restricted= P)
        reflexive (a constraint _) = eq-restricted (reflexive-on A a)
        
        transitive : Transitive (Restricted= P)
        transitive (eq-restricted a=b) (eq-restricted b=c) = eq-restricted (transitive-on A a=b b=c)

        symmetric : Symmetric (Restricted= P)
        symmetric (eq-restricted a=b) = eq-restricted (symmetric-on A a=b)
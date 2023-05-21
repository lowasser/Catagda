module Definitions.Category.One where

open import Agda.Primitive
open import Definitions.Logic
open import Definitions.Category
open import Definitions.Relation
open import Agda.Builtin.Unit

data OneMorph : ⊤ → ⊤ → Set where
    the-morph : OneMorph tt tt

open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence.Structural.Properties ⊤
open import Definitions.Relation.Equivalence.Structural.Properties (OneMorph tt tt) renaming (≡-Equivalence to morph-equivalence)

instance
    OneCategory : Category ⊤ OneMorph
    OneCategory = record {
            _∘_ = λ the-morph the-morph → the-morph;
            _=→_ = λ {tt} {tt} → _≡_;
            identity-arrow = λ tt → the-morph;
            left-congruent-arrow = λ _ morph → morph;
            right-congruent-arrow = λ _ morph → morph;
            associative-law = λ _ _ _ → refl;
            left-identity-law = λ _ → refl;
            right-identity-law = right-id-law;
            =→-equivalence = λ {tt} {tt} → morph-equivalence;
            =→-left-congruence = λ _ refl → refl;
            =→-right-congruence = λ _ refl → refl}
        where   right-id-law : {a b : ⊤} (f : OneMorph a b) → the-morph ≡ f
                right-id-law {tt} {tt} the-morph = refl

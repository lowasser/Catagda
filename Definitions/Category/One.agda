module Definitions.Category.One where

open import Agda.Primitive
open import Definitions.Category
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
            _=Arrow_ = λ {tt} {tt} → _≡_;
            identity-arrow = λ tt → the-morph;
            left-congruent-arrow = λ _ morph → morph;
            right-congruent-arrow = λ _ morph → morph;
            associative-law = λ _ _ _ → refl;
            left-identity-law = λ _ → refl;
            right-identity-law = right-id-law;
            =Arrow-equivalence = λ {tt} {tt} → morph-equivalence;
            =Arrow-left-congruence = λ _ refl → refl;
            =Arrow-right-congruence = λ _ refl → refl;
            left-congruent-compose = left-congruent-compose;
            right-congruent-compose = right-congruent-compose}
        where   right-id-law : {a b : ⊤} (f : OneMorph a b) → the-morph ≡ f
                right-id-law {tt} {tt} the-morph = refl
                right-congruent-compose : {a b c : ⊤} {bc1 bc2 : OneMorph b c} → bc1 ≡ bc2 → (ab : OneMorph a b) → ab ≡ ab
                right-congruent-compose _ the-morph = refl
                left-congruent-compose : {a b c : ⊤} {ab1 ab2 : OneMorph a b} → ab1 ≡ ab2 → (bc : OneMorph b c) → ab1 ≡ ab2
                left-congruent-compose refl _ = refl
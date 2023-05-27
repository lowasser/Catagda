module Structure.Category.Zero where

open import Agda.Primitive
open import Logic
open import Structure.Category
open import Relation

data ZeroMorph : ⊥ → ⊥ → Set where

open import Relation.Equivalence.Structural.Properties ⊥

instance
    ZeroCat : Category {lzero} {lzero} {lzero} {lzero} ⊥ ZeroMorph
    ZeroCat = record {
        _∘_ = λ ();
        left-congruent-arrow = λ _ ();
        _=Arrow_ = λ _ ();
        =Arrow-equivalence = λ {};
        =Arrow-left-congruence = λ {};
        =Arrow-right-congruence = λ {};
        right-congruent-arrow = λ {};
        identity-arrow = λ ();
        left-identity-law = λ {};
        right-identity-law = λ {};
        associative-law = λ {}}
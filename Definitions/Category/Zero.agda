module Definitions.Category.Zero where

open import Agda.Primitive
open import Definitions.Logic
open import Definitions.Category
open import Definitions.Relation

data ZeroMorph : ⊥ → ⊥ → Set where

open import Definitions.Relation.Equivalence.Structural.Properties ⊥

instance
    ZeroCat : Category {lzero} {lzero} {lzero} {lzero} ⊥ ZeroMorph
    ZeroCat = record {
        _∘_ = λ ();
        left-congruent-arrow = λ _ ();
        _=→_ = λ _ ();
        =→-equivalence = λ {};
        =→-left-congruence = λ {};
        =→-right-congruence = λ {};
        right-congruent-arrow = λ {};
        identity-arrow = λ ();
        left-identity-law = λ {};
        right-identity-law = λ {};
        associative-law = λ {}}
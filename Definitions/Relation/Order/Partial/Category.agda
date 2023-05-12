open import Agda.Primitive
open import Definitions.Setoid
open import Definitions.Relation
open import Definitions.Relation.Order.Partial

module Definitions.Relation.Order.Partial.Category {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} (_≤_ : Relation A) {{PO : PartialOrder _≤_}} where

open import Definitions.Category
open import Definitions.Relation.Properties

private
    _∘_ : { a b c : A } → b ≤ c → a ≤ b → a ≤ c
    b≤c ∘ a≤b = transitive-order-on _≤_ a≤b b≤c

open PartialOrder {{...}}

import Definitions.Relation.Equivalence.AllEqual 
open import Definitions.Relation.Equivalence.AllEqual using (eq; alleq-equivalence)

_==_ : {a b : A} → Relation (a ≤ b)
_==_ {a} {b} = Definitions.Relation.Equivalence.AllEqual._==_ (a ≤ b)

instance
    ≤-Category : Category A _≤_
    ≤-Category = record {
        _∘_ = _∘_;
        left-congruent-arrow = left-congruent-law;
        right-congruent-arrow = right-congruent-law;
        _=→_ = _==_;
        =→-equivalence = λ {a b} → alleq-equivalence (a ≤ b);
        identity-arrow = reflexive-order-on _≤_;
        left-identity-law = λ _ → eq;
        right-identity-law = λ _ → eq;
        associative-law = λ _ _ _ → eq;
        =→-left-congruence = λ _ _ → eq;
        =→-right-congruence = λ _ _ → eq}
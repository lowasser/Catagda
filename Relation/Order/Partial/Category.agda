open import Agda.Primitive
open import Structure.Setoid
open import Relation
open import Relation.Order.Partial

module Relation.Order.Partial.Category {ℓ : Level} (A : Set ℓ) {{SA : Setoid ℓ A}} (_≤_ : Relation A) {{PO : PartialOrder _≤_}} where

open import Structure.Category
open import Relation.Properties

private
    _∘_ : { a b c : A } → b ≤ c → a ≤ b → a ≤ c
    b≤c ∘ a≤b = transitive-order-on _≤_ a≤b b≤c

open PartialOrder {{...}}

import Relation.Equivalence.AllEqual 
open import Relation.Equivalence.AllEqual using (eq; alleq-equivalence)

_==_ : {a b : A} → Relation (a ≤ b)
_==_ {a} {b} = Relation.Equivalence.AllEqual._==_ (a ≤ b)

instance
    ≤-Category : Category A _≤_
    ≤-Category = record {
        _∘_ = _∘_;
        left-congruent-arrow = left-congruent-law;
        right-congruent-arrow = right-congruent-law;
        _=Arrow_ = _==_;
        =Arrow-equivalence = λ {a b} → alleq-equivalence (a ≤ b);
        identity-arrow = reflexive-order-on _≤_;
        left-identity-law = λ _ → eq;
        right-identity-law = λ _ → eq;
        associative-law = λ _ _ _ → eq;
        =Arrow-left-congruence = λ _ _ → eq;
        =Arrow-right-congruence = λ _ _ → eq}
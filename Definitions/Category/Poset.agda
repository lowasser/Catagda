open import Agda.Primitive

module Definitions.Category.Poset {ℓ : Level} where

open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Order.Partial
open import Definitions.Setoid
open import Definitions.Function.Properties
open import Definitions.Relation.Equivalence.Structural

record PosetOb : Set (lsuc ℓ) where
    field
        elements : Set ℓ
        _≤_ : Rel ℓ elements
        {{setoid}} : Setoid ℓ elements
        {{partial-order}} : PartialOrder _≤_

open PosetOb

record PosetMorph (POA POB : PosetOb) : Set (lsuc ℓ) where
    field
        function : elements POA Congruent→ elements POB
        monotonic : ∀ {a1 a2} → _≤_ POA a1 a2 → _≤_ POB (function cong$ a1) (function cong$ a2)

open PosetMorph

private
    _∘_ : {POA POB POC : PosetOb} → PosetMorph POB POC → PosetMorph POA POB → PosetMorph POA POC
    _∘_ {POA} {POB} {POC} f g = record {
        function = function f cong∘ function g;
        monotonic = λ a1≤a2 → monotonic f (monotonic g a1≤a2)}

    id-morph : (PO : PosetOb) → PosetMorph PO PO
    id-morph PO = record {
        function = id-congruent (elements PO);
        monotonic = λ a1≤a2 → a1≤a2 }

open import Definitions.Category.StructurePreserving
    {ℓ}
    PosetOb
    elements
    setoid
    PosetMorph
    function
    id-morph
    (λ _ → refl)
    _∘_
    (λ _ _ → refl)
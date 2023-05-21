open import Agda.Primitive

module Definitions.Category.Mon {ℓ : Level} where

open import Definitions.Monoid
open import Definitions.Function.Binary
open import Definitions.Setoid
open import Definitions.Category
open import Definitions.Function.Unary.Properties
open import Definitions.Setoid.Equation
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Function.Properties

record MonOb : Set (lsuc ℓ) where
    field
        elements : Set ℓ
        {{setoid}} : Setoid ℓ elements
        _∙_ : BinOp elements
        identity : elements
        {{monoid}} : Monoid _∙_ identity

open import Definitions.Relation.Equivalence.Structural
open MonOb
open Setoid

record MonHom (MA MB : MonOb) : Set (lsuc ℓ) where
    field
        function : (elements MA) Congruent→ (elements MB)
        identity-to-identity : _≅_ (setoid MB) (function cong$ identity MA) (identity MB)
        distributes : (a b : elements MA) → _≅_ (setoid MB) (function cong$ (_∙_ MA a b)) (_∙_ MB (function cong$ a) (function cong$ b))

data =MonHom (MA MB : MonOb) : Rel ℓ (MonHom MA MB) where
    =-mon-hom : {a b : MonHom MA MB} → ≡→ (elements MA) (elements MB) (MonHom.function a) (MonHom.function b) → =MonHom MA MB a b

open MonHom
open _Congruent→_

private
    _∘_ : {MA MB MC : MonOb} → MonHom MB MC → MonHom MA MB → MonHom MA MC
    _∘_ {MA} {MB} {MC} b→c a→b = record {
        function = function b→c cong∘ function a→b;
        identity-to-identity = begin≅
            function b→c cong$ (function a→b cong$ identity MA) ≅< is-congruent (function b→c) (identity-to-identity a→b) >
            function b→c cong$ identity MB                      ≅< identity-to-identity b→c >
            identity MC                                         ∎;
        distributes = λ a1 a2 → begin≅
            function b→c cong$ (function a→b cong$ (_∙_ MA a1 a2))                  ≅< is-congruent (function b→c) (distributes a→b a1 a2) >
            function b→c cong$ (_∙_ MB (function a→b cong$ a1) (function a→b cong$ a2))
                                                                                    ≅< distributes b→c (function a→b cong$ a1) (function a→b cong$ a2) >
            _∙_ MC (function b→c cong$ (function a→b cong$ a1)) (function b→c cong$ (function a→b cong$ a2))
                                                                                    ∎}

    id-monhom : (MA : MonOb) → MonHom MA MA
    id-monhom MA = record {
        function = id-congruent (elements MA);
        identity-to-identity = reflexive-on (elements MA) (identity MA);
        distributes = λ a1 a2 → reflexive-on (elements MA) (_∙_ MA a1 a2)}

open import Definitions.Category.StructurePreserving
    MonOb
    MonOb.elements
    MonOb.setoid
    MonHom
    MonHom.function
    id-monhom
    (λ _ → refl)
    _∘_
    (λ _ _ → refl)
open import Agda.Primitive

module Definitions.Setoid where

open import Definitions.Relation
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Properties

record Setoid { L : Level } (A : Set L) : Set (Agda.Primitive.lsuc L) where
    field
        _≈_ : Relation A
        {{≈_equivalence}} : Equivalence _≈_
        
    infix 4 _≈_

open Setoid {{...}}
open Equivalence {{...}}
open IsSymmetric {{...}}
open IsReflexive {{...}}
open IsTransitive {{...}}

symmetric-on : {ℓ : Level} → (A : Set ℓ) → {{SA : Setoid A}} → Symmetric _≈_
symmetric-on _ = symmetric

reflexive-on : {ℓ : Level} → (A : Set ℓ) → {{SA : Setoid A}} → Reflexive _≈_
reflexive-on _ = reflexive

transitive-on : {ℓ : Level} → (A : Set ℓ) → {{SA : Setoid A}} → Transitive _≈_
transitive-on _ = transitive
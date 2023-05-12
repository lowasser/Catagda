module Definitions.Nat where

open import Definitions.Setoid

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

open import Definitions.Function.Unary.Properties
open import Definitions.Relation
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence.Structural.Properties(ℕ)
open import Definitions.Relation.Order.Partial
open import Definitions.Relation.Order.Total
open import Definitions.Relation.Properties
open import Definitions.Either

instance
    ℕ-Setoid : Setoid ℕ
    ℕ-Setoid = record { _≈_ = _≡_ }

    ℕ-suc-congruent : IsCongruent suc
    ℕ-suc-congruent = record {congruent = ≡-congruent suc}

open Setoid {{...}}

data _≤_ : Relation ℕ where
    z≤ : { n : ℕ } → zero ≤ n
    s≤s : { a b : ℕ } → a ≤ b → suc a ≤ suc b

private
    s≈s : {a b : ℕ} → a ≈ b → suc a ≈ suc b
    s≈s refl = refl

    ≤-reflexive : Reflexive _≤_
    ≤-reflexive 0 = z≤
    ≤-reflexive (suc n) = s≤s (≤-reflexive n)

    ≤-transitive : Transitive _≤_
    ≤-transitive z≤ _ = z≤
    ≤-transitive (s≤s xy) (s≤s yz) = s≤s (≤-transitive xy yz)

    ≤-antisymmetric : Antisymmetric _≤_
    ≤-antisymmetric z≤ z≤ = refl
    ≤-antisymmetric (s≤s xy) (s≤s yx) = s≈s (≤-antisymmetric xy yx)

    ≤-compare : (x y : ℕ) → Either (x ≤ y) (y ≤ x)
    ≤-compare 0 _ = left z≤
    ≤-compare (suc x) (suc y) with ≤-compare x y
    ... | left x≤y  = left (s≤s x≤y)
    ... | right y≤x = right (s≤s y≤x)
    ≤-compare _ 0 = right z≤

    ≤-left-congruent : {a1 a2 b : ℕ} → a1 ≈ a2 → a1 ≤ b → a2 ≤ b
    ≤-left-congruent refl le = le

    ≤-right-congruent : {a b1 b2 : ℕ} → a ≤ b1 → b1 ≈ b2 → a ≤ b2
    ≤-right-congruent le refl = le

instance
    ≤-IsReflexive : IsReflexive _≤_
    ≤-IsReflexive = record { reflexive = ≤-reflexive }

    ≤-IsAntisymmetric : IsAntisymmetric _≤_
    ≤-IsAntisymmetric = record { antisymmetric = ≤-antisymmetric }

    ≤-IsTransitive : IsTransitive _≤_
    ≤-IsTransitive = record { transitive = ≤-transitive }

    ≤-PartialOrder : PartialOrder _≤_
    ≤-PartialOrder = record {left-congruent-law = ≤-left-congruent; right-congruent-law = ≤-right-congruent}

    ≤-TotalOrder : TotalOrder _≤_
    ≤-TotalOrder = record { compare = ≤-compare }
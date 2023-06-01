module Data.Number.Nat.Positive where

open import Agda.Primitive
open import Predicate
open import Predicate.Properties
open import Data.Number.Nat.Base
open import Data.Number.Nat.Order
open import Relation.Equivalence.Structural
open import Data.Number.Nat.Addition
open import Data.Number.Nat.Multiplication

data Positive : Predicate lzero ℕ where
    positive : (m : ℕ) → Positive (suc m)

private
    1≤-implies-positive : {n : ℕ} → 1ℕ ≤ n → Positive n
    1≤-implies-positive {suc n} _ = positive n

    positive-implies-1≤ : {n : ℕ} → Positive n → 1ℕ ≤ n
    positive-implies-1≤ (positive n) = s≤s 0≤

instance
    iff-positive-1≤ : Iff Positive (1ℕ ≤_)
    iff-positive-1≤ = record {implication→ = λ _ → positive-implies-1≤; implication← = λ _ → 1≤-implies-positive}

    iff-1≤-positive : Iff (1ℕ ≤_) Positive
    iff-1≤-positive = Iff.commute iff-positive-1≤

private
    pos-+-pos-is-pos : (a b : ℕ) → Positive a → Positive b → Positive (a + b)
    pos-+-pos-is-pos _ _ (positive m) (positive n) = positive (m + suc n)

    pos-*-pos-is-pos : (a b : ℕ) → Positive a → Positive b → Positive (a * b)
    pos-*-pos-is-pos _ _ (positive m) (positive n) = positive (n + (m * suc n))

    pos1 : Positive 1ℕ
    pos1 = positive 0ℕ

open import Structure.Setoid.Restricted ℕ Positive public

open import Structure.Algebraic.Semigroup.Commutative.Restricted _+_ Positive pos-+-pos-is-pos
    renaming 
        (restricted-op to _+⁺_; 
            restricted-bi-congruent to +⁺-bi-congruent; 
            restricted-commutative-semigroup to +⁺-commutative-semigroup;
            restricted-op-commutative-magma to +⁺-commutative-magma;
            restricted-op-is-associative to +⁺-is-associative;
            restricted-op-is-commutative to +⁺-is-commutative;
            restricted-op-semigroup to +⁺-semigroup;
            restricted-op-magma to +⁺-magma)
    public

open import Structure.Algebraic.Monoid.Commutative.Restricted _*_ 1ℕ Positive pos-*-pos-is-pos pos1
    renaming 
        (restricted-op to _*⁺_; 
            restricted-bi-congruent to *⁺-bi-congruent; 
            restricted-commutative-semigroup to *⁺-commutative-semigroup;
            restricted-op-commutative-magma to *⁺-commutative-magma;
            restricted-op-is-associative to *⁺-is-associative;
            restricted-op-is-commutative to *⁺-is-commutative;
            restricted-op-semigroup to *⁺-semigroup;
            restricted-op-magma to *⁺-magma)
    public
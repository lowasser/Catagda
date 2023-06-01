module Data.Number.Int.Positive where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Nat.Base using (ℕ; 0ℕ; 1ℕ; suc) renaming (_≅_ to _=N_)
open import Data.Number.Int.Base 
open import Data.Number.Int.Addition
open import Data.Number.Int.Multiplication
open import Data.Number.Int.Order
open import Data.Number.Nat.Order using (0≤; ordering-to-subtraction; s≤s) renaming (_≤_ to _≤N_)
open import Data.Number.Nat.Addition renaming (_+_ to _+N_)
open import Data.Number.Nat.Multiplication renaming (_*_ to _*N_)
open import Predicate
open import Predicate.Properties
open import Relation.Order.Partial
open import Structure.Setoid
open import Function.Binary.Properties
open import Structure.Setoid.Equation
open import Structure.Algebraic.Semigroup.Commutative

data Positive : Predicate lzero ℤ where
    positive : (x : ℤ) (n : ℕ) → x ≅ ℕ-to-ℤ (suc n) → Positive x

private
    1≤ℕ : (n : ℕ) → 1ℤ ≤ ℕ-to-ℤ (suc n)
    1≤ℕ n = z≤ (s≤s 0≤)

    positive-implies-1≤ : {x : ℤ} → Positive x → 1ℤ ≤ x
    positive-implies-1≤ (positive x n x=sn) = left-congruent-on-order _≤_ (symmetric-on ℤ x=sn) (z≤ (s≤s 0≤))

    helper : (a b : ℕ) → 1ℤ ≤ int a b → suc b ≤N a
    helper a b (z≤ sb≤a0) = left-congruent-on-order _≤N_ (right-identity-on _+N_ a) sb≤a0

    1≤-implies-positive : {x : ℤ} → 1ℤ ≤ x → Positive x
    1≤-implies-positive {int p n} cmp with ordering-to-subtraction (helper p n cmp)
    ... | m , snm=p = positive (int p n) m (z= (begin≅
        p +N 0ℕ         ≅< right-identity-on _+N_ p >
        p               ≅< symmetric-on ℕ snm=p >
        (1ℕ +N n) +N m  ≅< <ab>c-to-<ac>b-on _+N_ 1ℕ n m >
        suc m +N n      ∎))

instance
    iff-positive-1≤ : Iff Positive (1ℤ ≤_)
    iff-positive-1≤ = record {implication→ = λ _ → positive-implies-1≤; implication← = λ _ → 1≤-implies-positive}

    iff-0≤-nonnegative : Iff (1ℤ ≤_) Positive
    iff-0≤-nonnegative = Iff.commute iff-positive-1≤

private
    positive-+-is-positive : (a b : ℤ) → Positive a → Positive b → Positive (a + b)
    positive-+-is-positive _ _ (positive a m a=sm) (positive b n b=sn) = positive (a + b) (m +N suc n) (bi-congruent _+_ a=sm b=sn)

    *-lemma : (a b : ℕ) → ℕ-to-ℤ a * ℕ-to-ℤ b ≅ ℕ-to-ℤ (a *N b)
    *-lemma a b = z= (begin≅
        (a *N b +N 0ℕ *N 0ℕ) +N 0ℕ      ≅< right-associate-on _+N_ (a *N b) 0ℕ 0ℕ >
        a *N b +N (0ℕ +N 0ℕ)            ≅< left-congruent-on _+N_ {a *N b} (right-congruent-on _+N_ {0ℕ} (symmetric-on ℕ (right-zero-on _*N_ 0ℕ a))) >
        a *N b +N (a *N 0ℕ +N 0ℕ)       ∎)

    positive-*-is-positive : (a b : ℤ) → Positive a → Positive b → Positive (a * b)
    positive-*-is-positive _ _ (positive a m a=sm) (positive b n b=sn) = positive (a * b) (n +N m *N suc n) (begin≅
        a * b                                ≅< bi-congruent _*_ a=sm b=sn >
        ℕ-to-ℤ (suc m) * ℕ-to-ℤ (suc n)     ≅< *-lemma (suc m) (suc n) >
        ℕ-to-ℤ (suc (n +N m *N suc n))      ∎)

    1-positive : Positive 1ℤ
    1-positive = positive 1ℤ 0ℕ (reflexive-on ℤ 1ℤ)

open import Structure.Algebraic.Semigroup.Commutative.Restricted _+_ Positive positive-+-is-positive
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

open import Structure.Algebraic.Monoid.Commutative.Restricted _*_ 1ℤ Positive positive-*-is-positive 1-positive
    renaming 
        (restricted-op to _*⁺_; 
            restricted-identity to 1ℤ⁺;
            restricted-bi-congruent to *⁺-bi-congruent; 
            restricted-has-identity to *⁺-has-identity; 
            restricted-commutative-monoid to *⁺-commutative-monoid;
            restricted-commutative-semigroup to *⁺-commutative-semigroup;
            restricted-op-commutative-magma to *⁺-commutative-magma;
            restricted-op-is-associative to *⁺-is-associative;
            restricted-op-is-commutative to *⁺-is-commutative;
            restricted-op-semigroup to *⁺-semigroup;
            restricted-monoid to *⁺-monoid;
            restricted-op-magma to *⁺-magma)
    public
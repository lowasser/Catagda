module Data.Number.Int.Nonnegative where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Nat.Base using (ℕ; 0ℕ; 1ℕ) renaming (_≅_ to _=N_)
open import Data.Number.Int.Base 
open import Data.Number.Int.Addition
open import Data.Number.Int.Multiplication
open import Data.Number.Int.Order
open import Data.Number.Nat.Order using (0≤; ordering-to-subtraction) renaming (_≤_ to _≤N_)
open import Data.Number.Nat.Addition renaming (_+_ to _+N_)
open import Data.Number.Nat.Multiplication renaming (_*_ to _*N_)
open import Predicate
open import Predicate.Properties
open import Relation.Order.Partial
open import Structure.Setoid
open import Function.Binary.Properties
open import Structure.Setoid.Equation

data Nonnegative : Predicate lzero ℤ where
    nonnegative : (x : ℤ) (n : ℕ) → x ≅ ℕ-to-ℤ n → Nonnegative x

private
    0≤ℕ : (n : ℕ) → 0ℤ ≤ ℕ-to-ℤ n
    0≤ℕ n = z≤ 0≤

    nonnegative-implies-0≤ : {x : ℤ} → Nonnegative x → 0ℤ ≤ x
    nonnegative-implies-0≤ (nonnegative x n x=n) = left-congruent-on-order _≤_ (symmetric-on ℤ x=n) (0≤ℕ n)

    helper : (a b : ℕ) → 0ℤ ≤ int a b → b ≤N a
    helper a b (z≤ 0b≤a0) = bi-congruent-order _≤N_ (symmetric-on ℕ (left-identity-on _+N_ b)) (symmetric-on ℕ (right-identity-on _+N_ a)) 0b≤a0

    0≤-implies-nonnegative : {x : ℤ} → 0ℤ ≤ x → Nonnegative x
    0≤-implies-nonnegative {int p n} cmp with ordering-to-subtraction (helper p n cmp)
    ... | m , eq = nonnegative (int p n) m (z= (begin≅ 
            p +N 0ℕ             ≅< right-identity-on _+N_ p >
            p                   ≅< symmetric-on ℕ eq >
            n +N m              ≅< commute-on _+N_ n m >
            m +N n              ∎))

instance
    iff-nonnegative-0≤ : Iff Nonnegative (0ℤ ≤_)
    iff-nonnegative-0≤ = record {implication→ = λ _ → nonnegative-implies-0≤ ; implication← = λ _ → 0≤-implies-nonnegative}

    iff-0≤-nonnegative : Iff (0ℤ ≤_) Nonnegative
    iff-0≤-nonnegative = Iff.commute iff-nonnegative-0≤

private
    nonneg-+-is-nonneg : (a b : ℤ) → Nonnegative a → Nonnegative b → Nonnegative (a + b)
    nonneg-+-is-nonneg _ _ (nonnegative a m a=m) (nonnegative b n b=n) = nonnegative (a + b) (m +N n) (bi-congruent _+_ a=m b=n)

    *-lemma : (a b : ℕ) → ℕ-to-ℤ a * ℕ-to-ℤ b ≅ ℕ-to-ℤ (a *N b)
    *-lemma a b = z= (begin≅
        (a *N b +N 0ℕ *N 0ℕ) +N 0ℕ      ≅< right-associate-on _+N_ (a *N b) 0ℕ 0ℕ >
        a *N b +N (0ℕ +N 0ℕ)            ≅< left-congruent-on _+N_ {a *N b} (right-congruent-on _+N_ {0ℕ} (symmetric-on ℕ (right-zero-on _*N_ 0ℕ a))) >
        a *N b +N (a *N 0ℕ +N 0ℕ)       ∎)

    nonneg-*-is-nonneg : (a b : ℤ) → Nonnegative a → Nonnegative b → Nonnegative (a * b)
    nonneg-*-is-nonneg _ _ (nonnegative a m a=m) (nonnegative b n b=n) = nonnegative (a * b) (m *N n) (begin≅
        a * b                       ≅< bi-congruent _*_ a=m b=n >
        ℕ-to-ℤ m * ℕ-to-ℤ n         ≅< *-lemma m n >
        ℕ-to-ℤ (m *N n)             ∎)

    1-nonneg : Nonnegative 1ℤ
    1-nonneg = nonnegative 1ℤ 1ℕ (reflexive-on ℤ 1ℤ)

    0-nonneg : Nonnegative 0ℤ
    0-nonneg = nonnegative 0ℤ 0ℕ (reflexive-on ℤ 0ℤ)

open import Structure.Algebraic.Monoid.Commutative.Restricted _+_ 0ℤ Nonnegative nonneg-+-is-nonneg 0-nonneg
    renaming 
        (restricted-op to _+⁰⁺_; 
            restricted-identity to 0ℤ⁰⁺;
            restricted-bi-congruent to +⁰⁺-bi-congruent; 
            restricted-has-identity to +⁰⁺-has-identity; 
            restricted-commutative-monoid to +⁰⁺-commutative-monoid;
            restricted-commutative-semigroup to +⁰⁺-commutative-semigroup;
            restricted-op-commutative-magma to +⁰⁺-commutative-magma;
            restricted-op-is-associative to +⁰⁺-is-associative;
            restricted-op-is-commutative to +⁰⁺-is-commutative;
            restricted-op-semigroup to +⁰⁺-semigroup;
            restricted-monoid to +⁰⁺-monoid;
            restricted-op-magma to +⁰⁺-magma)
    public

open import Structure.Algebraic.Monoid.Commutative.Restricted _*_ 1ℤ Nonnegative nonneg-*-is-nonneg 1-nonneg
    renaming 
        (restricted-op to _*⁰⁺_; 
            restricted-identity to 1ℤ⁰⁺;
            restricted-bi-congruent to *⁰⁺-bi-congruent; 
            restricted-has-identity to *⁰⁺-has-identity; 
            restricted-commutative-monoid to *⁰⁺-commutative-monoid;
            restricted-commutative-semigroup to *⁰⁺-commutative-semigroup;
            restricted-op-commutative-magma to *⁰⁺-commutative-magma;
            restricted-op-is-associative to *⁰⁺-is-associative;
            restricted-op-is-commutative to *⁰⁺-is-commutative;
            restricted-op-semigroup to *⁰⁺-semigroup;
            restricted-monoid to *⁰⁺-monoid;
            restricted-op-magma to *⁰⁺-magma)
    public
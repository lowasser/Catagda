module Definitions.Nat.Addition.Properties where

open import Agda.Primitive
open import Definitions.Nat
open import Definitions.Nat.Addition
open import Definitions.Function.Unary.Properties
open import Definitions.Function.Binary.Properties
open import Definitions.Relation.Properties
open import Definitions.Setoid
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Setoid.Equation
open import Definitions.Relation.Equivalence.Structural.Properties(ℕ)
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid
open import Definitions.Monoid.Commutative

open Setoid {{...}}
open Equivalence {{...}}
open IsReflexive {{...}}
open IsSymmetric {{...}}

instance
    +ℕ-BiCongruent : BiCongruent _+_
    +ℕ-BiCongruent = ≡-bi-congruent _+_

    +ℕ-Magma : Magma _+_
    +ℕ-Magma = record {}

private
    +-commute-lemma : (m n : ℕ) → m + suc n ≈ suc (m + n)
    +-commute-lemma zero n = begin≈
        zero + suc n        ≈<>
        suc n               ≈<>
        suc (zero + n)      ∎
    +-commute-lemma (suc m) n = begin≈
        suc m + suc n       ≈<>
        suc (m + suc n)     ≈< congruent-on suc (+-commute-lemma m n) >
        suc (suc (m + n))   ≈<>
        suc (suc m + n)     ∎

    +-left-id : LeftIdentity _+_ 0
    +-left-id _ = refl

    +-right-id : RightIdentity _+_ 0
    +-right-id zero     = refl
    +-right-id (suc n)  = begin≈
        suc n + 0       ≈<>
        suc (n + 0)     ≈< congruent-on suc (+-right-id n) >
        suc n           ∎

instance
    +ℕ-identity : HasIdentity _+_ 0
    +ℕ-identity = record {left-identity = +-left-id; right-identity = +-right-id}

private
    +-commute : Commute _+_
    +-commute 0 n = begin≈
        0 + n       ≈<>
        n           ≈< symmetric (+-right-id n) >
        n + 0       ∎
    +-commute (suc m) n = begin≈
        suc m + n   ≈<>
        suc (m + n) ≈< congruent-on suc (+-commute m n) >
        suc (n + m) ≈< symmetric (+-commute-lemma n m) >
        n + suc m   ∎

instance
    +ℕ-is-commutative : IsCommutative _+_
    +ℕ-is-commutative = record {commute = +-commute }

    +ℕ-CommutativeMagma : CommutativeMagma _+_
    +ℕ-CommutativeMagma = record {}

private
    +-assoc : Associate _+_
    +-assoc 0 y z = begin≈
        0 + (y + z)     ≈<>
        y + z           ≈< right-congruent-on _+_ (symmetric (+-left-id y)) >
        (0 + y) + z     ∎  
    +-assoc (suc x) y z = begin≈
        suc x + (y + z)     ≈<>
        suc (x + (y + z))   ≈< congruent-on suc (+-assoc x y z) >
        suc ((x + y) + z)   ≈<>
        suc (x + y) + z     ≈<>
        (suc x + y) + z     ∎

instance
    +ℕ-is-associative : IsAssociative _+_
    +ℕ-is-associative = record { associate = +-assoc }

    +ℕ-Semigroup : Semigroup _+_
    +ℕ-Semigroup = record {}

    +ℕ-CommutativeSemigroup : CommutativeSemigroup _+_
    +ℕ-CommutativeSemigroup = record {}

    +ℕ-Monoid : Monoid _+_ 0
    +ℕ-Monoid = record {}

    +ℕ-CommutativeMonoid : CommutativeMonoid _+_ 0
    +ℕ-CommutativeMonoid = record {}

private
    unsuc≡ : {a b : ℕ} → (suc a ≡ suc b) → a ≡ b
    unsuc≡ refl = refl

+ℕ-left-injective : (a : ℕ) → Injective (a +_)
+ℕ-left-injective 0 {b} {c} 0b≡0c = begin≈
    b       ≈<>
    0 + b   ≈< 0b≡0c >
    0 + c   ≈<>
    c       ∎
+ℕ-left-injective (suc a) {b} {c} sucab≡sucac = unsuc≡ (+ℕ-left-injective a (begin≈
    a + suc b       ≈< +-commute-lemma a b >
    suc (a + b)     ≈<>
    suc a + b       ≈< sucab≡sucac >
    suc a + c       ≈<>
    suc (a + c)     ≈< symmetric (+-commute-lemma a c) >
    a + suc c       ∎))

+ℕ-right-injective : (a : ℕ) → Injective (_+ a)
+ℕ-right-injective a {b} {c} ba≡ca = +ℕ-left-injective a (begin≈
    a + b       ≈< +-commute a b >
    b + a       ≈< ba≡ca >
    c + a       ≈< +-commute c a >
    a + c       ∎) 

≤ℕ-left-cancel-+ : { a b c : ℕ } → (a + b) ≤ (a + c) → b ≤ c
≤ℕ-left-cancel-+ {0} 0b≤0c = 0b≤0c
≤ℕ-left-cancel-+ {suc a} (s≤s ab≤ac) = ≤ℕ-left-cancel-+ ab≤ac
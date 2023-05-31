module Data.Number.Nat.Multiplication where

open import Structure.Setoid
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Relation.Equivalence.Structural.Properties ⊤
open import Data.List
open import Structure.Setoid.Equation
open import Function.Binary
open import Function.Binary.Properties
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Ringoid
open import Relation.Order.Partial
open import Relation.Order.Total
open import Data.Either
open import Data.Number.Nat.Base
open import Data.Number.Nat.Addition
open import Data.Number.Nat.Order

_*_ : BinOp ℕ
0ℕ * n = 0ℕ
suc m * n = n + (m * n)

infixr 10 _*_

private
    *-left-congruent : LeftCongruent _*_
    *-left-congruent {0ℕ}  _ = 0ℕ=
    *-left-congruent {suc a} {b} {c} b=c = bi-congruent _+_ b=c (*-left-congruent {a} {b} {c} b=c)

    *-left-zero : LeftZero _*_ 0ℕ
    *-left-zero _ = 0ℕ=

    *-right-zero : RightZero _*_ 0ℕ
    *-right-zero 0ℕ = 0ℕ=
    *-right-zero (suc n) = *-right-zero n

    *-distributes-over-+ : (a b c : ℕ) → a * (b + c) ≅ a * b + a * c
    *-distributes-over-+ 0ℕ _ _ = 0ℕ=
    *-distributes-over-+ (suc a) b c = begin≅
        suc a * (b + c)             ≅<>
        (b + c) + a * (b + c)       ≅< left-congruent-on _+_ (*-distributes-over-+ a b c) >
        (b + c) + (a * b + a * c)   ≅< right-congruent-on _+_ (commute-on _++_ b c) >
        (c + b) + (a * b + a * c)   ≅< left-associate-on _+_ (c + b) (a * b) (a * c) >
        ((c + b) + a * b) + a * c   ≅< right-congruent-on _+_ (right-associate-on _+_ c b (a * b)) >
        (c + (b + a * b)) + a * c   ≅<>
        (c + suc a * b) + a * c     ≅< right-congruent-on _+_ (commute-on _++_ c (suc a * b)) >
        (suc a * b + c) + a * c     ≅< right-associate-on _+_ (suc a * b) c (a * c) >
        suc a * b + (c + a * c)     ≅<>
        suc a * b + suc a * c       ∎

    *-left-id : LeftIdentity _*_ 1ℕ
    *-left-id 0ℕ = 0ℕ=
    *-left-id (suc n) = right-identity-on _+_ (suc n)

    *-right-id : RightIdentity _*_ 1ℕ
    *-right-id 0ℕ = 0ℕ=
    *-right-id (suc n) = left-congruent-on _+_ (*-right-id n)
    
    *-commute : Commute _*_
    *-commute 0ℕ n = symmetric-on ℕ (*-right-zero n)
    *-commute (suc m) n = begin≅
        suc m * n           ≅<>
        n + (m * n)         ≅< left-congruent-on _+_ (*-commute m n) >
        n + (n * m)         ≅< right-congruent-on _+_ (symmetric-on ℕ (*-right-id n)) >
        (n * 1ℕ) + (n * m)  ≅< symmetric-on ℕ (*-distributes-over-+ n 1ℕ m) >
        n * (1ℕ + m)        ≅<>
        n * suc m           ∎

    *-right-distributes : (a b c : ℕ) → (a + b) * c ≅ a * c + b * c
    *-right-distributes a b c = begin≅
        (a + b) * c         ≅< *-commute (a + b) c >
        c * (a + b)         ≅< *-distributes-over-+ c a b >
        c * a + c * b       ≅< bi-congruent _+_ (*-commute c a) (*-commute c b) >
        a * c + b * c       ∎

    *-assoc : Associate _*_
    *-assoc 0ℕ _ _ = 0ℕ=
    *-assoc (suc a) b c = begin≅
        suc a * (b * c)                     ≅<>
        b * c + a * (b * c)                 ≅< left-congruent-on _+_ (*-assoc a b c) >
        b * c + (a * b) * c                 ≅< symmetric-on ℕ (*-right-distributes b (a * b) c) >
        (b + a * b) * c                     ≅<>
        (suc a * b) * c                     ∎

        
instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record { commute = *-commute }

    *-bicong : BiCongruent _*_
    *-bicong = bi-congruent-commutative _*_ (λ {a b c} b=c → *-left-congruent {a} {b} {c} b=c)

    *-magma : Magma _*_
    *-magma = record {}

    *-commutative-magma : CommutativeMagma _*_
    *-commutative-magma = record {}

    *-is-associative : IsAssociative _*_
    *-is-associative = record { associate = *-assoc }

    *-semigroup : Semigroup _*_
    *-semigroup = record {}

    *-commutative-semigroup : CommutativeSemigroup _*_
    *-commutative-semigroup = record {}

    *-has-identity : HasIdentity _*_ 1ℕ
    *-has-identity = record { left-identity = *-left-id ; right-identity = *-right-id }

    *-monoid : Monoid _*_ 1ℕ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℕ
    *-commutative-monoid = record {}

    *-ringoid : Ringoid _*_ _+_
    *-ringoid = record { left-distribute = *-distributes-over-+ ; right-distribute = *-right-distributes }

    *-has-zero : HasZero _*_ 0ℕ
    *-has-zero = record {left-zero = *-left-zero; right-zero = *-right-zero}

cancel-right-multiplication-nonzero : {x y z : ℕ} → (y * suc x ≅ z * suc x) → y ≅ z
cancel-right-multiplication-nonzero {x} {suc y} {suc z} sysx=szsx = suc= (cancel-right-multiplication-nonzero (left-injective-on _+_ (suc x) sysx=szsx))
cancel-right-multiplication-nonzero {suc x} {0ℕ} {suc z} ()
cancel-right-multiplication-nonzero {suc x} {suc y} {0ℕ} ()
cancel-right-multiplication-nonzero {_} {0ℕ} {0ℕ} _ = 0ℕ=

cancel-left-multiplication-nonzero : {x y z : ℕ} → (suc x * y ≅ suc x * z) → y ≅ z
cancel-left-multiplication-nonzero {x} {y} {z} eq = cancel-right-multiplication-nonzero {x} {y} {z} (begin≅
    y * suc x   ≅< commute-on _*_ y (suc x) >
    suc x * y   ≅< eq >
    suc x * z   ≅< commute-on _*_ (suc x) z >
    z * suc x   ∎)

product-is-zero : {a b : ℕ} → (a * b ≅ 0ℕ) → Either (a ≅ 0ℕ) (b ≅ 0ℕ)
product-is-zero {0ℕ} {_} _ = left 0ℕ=
product-is-zero {_} {0ℕ} _ = right 0ℕ=
-- compiler can prove no other cases

multiplication-preserves-≤ : {a b c d : ℕ} → a ≤ b → c ≤ d → a * c ≤ b * d
multiplication-preserves-≤ {a} {b} {c} {d} a≤b c≤d with ordering-to-subtraction a≤b | ordering-to-subtraction c≤d
... | x , a+x=b | y , c+y=d = subtraction-to-ordering (symmetric-on ℕ (begin≅
        b * d                               ≅< bi-congruent _*_ (symmetric-on ℕ a+x=b) (symmetric-on ℕ c+y=d) >
        (a + x) * (c + y)                   ≅< left-distribute-on _*_ _+_ (a + x) c y >
        (a + x) * c + (a + x) * y           ≅< bi-congruent _+_ (right-distribute-on _*_ _+_ a x c) (right-distribute-on _*_ _+_ a x y) >
        (a * c + x * c) + (a * y + x * y)   ≅< right-associate-on _+_ (a * c) (x * c) (a * y + x * y) >
        a * c + (x * c + (a * y + x * y))   ∎))

cancel-right-multiplication-nonzero-≤ : {x y z : ℕ} → x * suc z ≤ y * suc z → x ≤ y
cancel-right-multiplication-nonzero-≤ {x} {y} {0ℕ} x1≤y1 = bi-congruent-order _≤_ (symmetric-on ℕ (right-identity-on _*_ x)) (symmetric-on ℕ (right-identity-on _*_ y)) x1≤y1
cancel-right-multiplication-nonzero-≤ {0ℕ} _ = 0≤
cancel-right-multiplication-nonzero-≤ {x} {0ℕ} xsz≤ysz = reflexive-equiv-order-on _≤_ (cancel-right-multiplication-nonzero-≤-lemma xsz≤ysz)
    where   cancel-right-multiplication-nonzero-≤-lemma : {x y : ℕ} → x * suc y ≤ 0ℕ → x ≅ 0ℕ
            cancel-right-multiplication-nonzero-≤-lemma {0ℕ} _ = 0ℕ=
cancel-right-multiplication-nonzero-≤ {suc x} {suc y} {z} xsz≤ysz = 
    s≤s (cancel-right-multiplication-nonzero-≤ (cancel-left-+-≤ (suc z) (x * suc z) (y * suc z) xsz≤ysz))

cancel-left-multiplication-nonzero-≤ : {x y z : ℕ} → suc x * y ≤ suc x * z → y ≤ z
cancel-left-multiplication-nonzero-≤ {x} {y} {z} sxy≤sxz = cancel-right-multiplication-nonzero-≤ (bi-congruent-order _≤_ (commute-on _*_ y (suc x)) (commute-on _*_ z (suc x)) sxy≤sxz)

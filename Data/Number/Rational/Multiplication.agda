module Data.Number.Rational.Multiplication where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Int.Base renaming (_≅_ to _=Z_; neg to negZ)
open import Data.Number.Int.Addition renaming (_+_ to _+Z_; left-+-preserves-≤ to left-+-preserves-≤N)
open import Data.Number.Int.Multiplication renaming (_*_ to _*Z_; *-nonnegative to *Z-nonnegative)
    hiding (*-bi-congruent; *-is-commutative; *-magma; *-commutative-magma; *-is-associative; *-semigroup; *-commutative-semigroup; *-has-identity; *-monoid; *-commutative-monoid;
            *-+-ringoid; *-+-ring; *-+-commutative-ring)
open import Function.Binary
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Relation
open import Data.Either
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Ring
open import Structure.Algebraic.Ring.Commutative
open import Data.Number.Rational
open import Structure.Algebraic.Semigroup.Commutative
open import Logic
open import Structure.Algebraic.IntegralDomain
open import Structure.Algebraic.Magma
open import Structure.Algebraic.Magma.Commutative
open import Structure.Algebraic.Semigroup
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Algebraic.Monoid
open import Structure.Algebraic.Monoid.Commutative
open import Structure.Algebraic.Group
open import Data.Number.Rational.Addition
open import Structure.Algebraic.Ringoid
open import Structure.Algebraic.Field
open import Relation.Order.Partial
open import Relation.Order.Total
open import Data.Number.Int.Order renaming (_≤_ to _≤Z_)
open import Data.Number.Nat.Order using (0≤)
open import Data.Number.Rational.Order

_*_ : BinOp ℚ
frac p q q≠0 0≤q * frac r s s≠0 0≤s = frac (p *Z r) (q *Z s) qs≠0 (right-congruent-on-order _≤Z_ (right-zero-on _*Z_ 0ℤ q) (left-multiplication-nonnegative 0≤q 0≤s))
    where   qs≠0 : ¬ (q *Z s) =Z 0ℤ
            qs≠0 qs=0 with product-is-zero-one-is-zero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ q s qs=0
            ... | left q=0  = q≠0 q=0
            ... | right s=0 = s≠0 s=0

private
    is-zero-implies-numerator-zero : {p q : ℤ} {q≠0 : ¬ (q =Z 0ℤ)} {0≤q : 0ℤ ≤Z q} → frac p q q≠0 0≤q ≅ 0ℚ → p =Z 0ℤ
    is-zero-implies-numerator-zero {p} {q} {q≠0} (q= eq) = begin≅
        p               ≅< symmetric-on ℤ (right-identity-on _*Z_ p) >
        p *Z 1ℤ         ≅< eq >
        0ℤ *Z q         ≅< left-zero-on _*Z_ 0ℤ q >
        0ℤ              ∎

private
    normalize-frac : (p q : ℤ) → ¬ (q =Z 0ℤ) → ℚ
    normalize-frac p q q≠0 with compare-order-on _≤Z_ 0ℤ q
    ... | left 0≤q      = frac p q q≠0 0≤q
    ... | right q≤0     = frac (negZ p) (negZ q) nq≠0 (neg-swaps-order q≤0)
        where   nq≠0 : ¬ (negZ q =Z 0ℤ)
                nq≠0 nq=0 = q≠0 (begin≅
                    q               ≅< symmetric-on ℤ (inverse-inverse-on _+Z_ 0ℤ negZ q) >
                    negZ (negZ q)   ≅< congruent-on negZ nq=0 >
                    negZ 0ℤ         ≅<>
                    0ℤ              ∎)

recip : (x : ℚ) → ¬ (x ≅ 0ℚ) → ℚ
recip (frac p q q≠0 0≤q) x≠0 = normalize-frac q p lemma where
    lemma : ¬ (p =Z 0ℤ)
    lemma p=0 = x≠0 (q= (begin≅
        p *Z 1ℤ     ≅< right-congruent-on _*Z_ p=0 >
        0ℤ *Z 1ℤ    ≅< symmetric-on ℤ (left-zero-on _*Z_ 0ℤ q) >
        0ℤ *Z q     ∎))

private
    recip-left-inverse : (x : ℚ) → (x≠0 : ¬ (x ≅ 0ℚ)) → (recip x x≠0 * x ≅ 1ℚ)
    recip-left-inverse (frac p q q≠0 0≤q) x≠0 with compare-order-on _≤Z_ 0ℤ p
    ... | left _ = q= (<ab>c-to-c<ba>-on _*Z_ q p 1ℤ)
    ... | right _ = q= (begin≅
        (negZ q *Z p) *Z 1ℤ     ≅< commute-on _*Z_ (negZ q *Z p) 1ℤ >
        1ℤ *Z (negZ q *Z p)     ≅< left-congruent-on _*Z_ (commute-times-neg-on _*Z_ _+Z_ 1ℤ 0ℤ negZ q p) >
        1ℤ *Z (q *Z negZ p)     ≅< left-congruent-on _*Z_ (commute-on _*Z_ q (negZ p)) >
        1ℤ *Z (negZ p *Z q)     ∎)

    *-left-congruent : LeftCongruent _*_
    *-left-congruent {frac p q _ _} {frac r s _ _} {frac t u _ _} (q= ru=ts) = q= (begin≅
        (p *Z r) *Z (q *Z u)        ≅< <ab><cd>-to-<ac><bd>-on _*Z_ p r q u >
        (p *Z q) *Z (r *Z u)        ≅< left-congruent-on _*Z_ ru=ts >
        (p *Z q) *Z (t *Z s)        ≅< <ab><cd>-to-<ac><bd>-on _*Z_ p q t s >
        (p *Z t) *Z (q *Z s)        ∎)

    *-commute : Commute _*_
    *-commute (frac p q _ _) (frac r s _ _) = q= (bi-congruent _*Z_ (commute-on _*Z_ p r) (commute-on _*Z_ s q))


instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record {commute = *-commute}

    *-bi-congruent : BiCongruent _*_
    *-bi-congruent = bi-congruent-commute _*_ *-left-congruent 

    *-magma : Magma _*_
    *-magma = record {}

    *-commutative-magma : CommutativeMagma _*_
    *-commutative-magma = record {}

private
    *-assoc : Associate _*_
    *-assoc (frac p q _ _) (frac r s _ _) (frac t u _ _) = q= (bi-congruent _*Z_ (left-associate-on _*Z_ p r t) (right-associate-on _*Z_ q s u))

instance
    *-is-associative : IsAssociative _*_ 
    *-is-associative = record {associate = *-assoc}

    *-semigroup : Semigroup _*_
    *-semigroup = record {}

    *-commutative-semigroup : CommutativeSemigroup _*_
    *-commutative-semigroup = record {}

private
    *-left-identity : LeftIdentity _*_ 1ℚ
    *-left-identity (frac p q _ _) = q= (<ab>c-to-b<ac>-on _*Z_ 1ℤ p q)

instance
    *-has-identity : HasIdentity _*_ 1ℚ
    *-has-identity = has-identity-commute *-left-identity

    *-monoid : Monoid _*_ 1ℚ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℚ
    *-commutative-monoid = record {}

private
    *-+-left-distribute : (a b c : ℚ) → a * (b + c) ≅ (a * b) + (a * c)
    *-+-left-distribute (frac p q _ _) (frac r s _ _) (frac t u _ _) = q= (begin≅
        (p *Z (r *Z u +Z t *Z s)) *Z ((q *Z s) *Z (q *Z u))     ≅< bi-congruent _*Z_ (left-distribute-on _*Z_ _+Z_ p (r *Z u) (t *Z s)) (right-associate-on _*Z_ q s (q *Z u)) >
        (p *Z (r *Z u) +Z p *Z (t *Z s)) *Z (q *Z (s *Z (q *Z u)))
                                                                ≅< right-congruent-on _*Z_ (bi-congruent _+Z_ (left-associate-on _*Z_ p r u) (left-associate-on _*Z_ p t s)) >
        ((p *Z r) *Z u +Z (p *Z t) *Z s) *Z (q *Z (s *Z (q *Z u)))
                                                                ≅< left-associate-on _*Z_ ((p *Z r) *Z u +Z (p *Z t) *Z s) q (s *Z (q *Z u)) >
        (((p *Z r) *Z u +Z (p *Z t) *Z s) *Z q) *Z (s *Z (q *Z u))
                                                                ≅< bi-congruent _*Z_ (right-distribute-on _*Z_ _+Z_ ((p *Z r) *Z u) ((p *Z t) *Z s) q) (a<bc>-to-b<ac>-on _*Z_ s q u) >
        (((p *Z r) *Z u) *Z q +Z ((p *Z t) *Z s) *Z q) *Z (q *Z (s *Z u))
                                                                ≅< right-congruent-on _*Z_ (bi-congruent _+Z_ (right-associate-on _*Z_ (p *Z r) u q) (right-associate-on _*Z_ (p *Z t) s q)) >
        ((p *Z r) *Z (u *Z q) +Z (p *Z t) *Z (s *Z q)) *Z (q *Z (s *Z u))
                                                                ≅< right-congruent-on _*Z_ (bi-congruent _+Z_ (left-congruent-on _*Z_ (commute-on _*Z_ u q)) (left-congruent-on _*Z_ (commute-on _*Z_ s q))) >
        ((p *Z r) *Z (q *Z u) +Z (p *Z t) *Z (q *Z s)) *Z (q *Z (s *Z u))
                                                                ∎)

instance
    *-+-ringoid : Ringoid _*_ _+_
    *-+-ringoid = commuting-ringoid *-+-left-distribute

    *-+-ring : Ring _*_ _+_ 1ℚ 0ℚ neg
    *-+-ring = record {}

    *-+-commutative-ring : CommutativeRing _*_ _+_ 1ℚ 0ℚ neg
    *-+-commutative-ring = record {}

    ℚ-field : Field _*_ _+_ 1ℚ 0ℚ recip neg
    ℚ-field = record {left-multiplicative-inverse = recip-left-inverse}


private
    2ℤ : ℤ
    2ℤ = 1ℤ +Z 1ℤ

    1/2ℚ : ℚ
    1/2ℚ = frac 1ℤ 2ℤ 2≠0 (z≤ 0≤) where
        2≠0 : ¬ (2ℤ =Z 0ℤ)
        2≠0 (z= ())

right-positive-*-≤ : {p q r : ℚ} → 0ℚ ≤ r → ¬ (r ≅ 0ℚ) → p ≤ q → p * r ≤ q * r
right-positive-*-≤ {frac a b b≠0 0≤b} {frac c d d≠0 0≤d} {frac e f f≠0 0≤f} (q≤ 0f≤e1) r≠0 (q≤ ad≤cb) = q≤ 
        (bi-congruent-order _≤Z_ (<ab><cd>-to-<bd><ac>-on _*Z_ a e d f) (<ab><cd>-to-<bd><ac>-on _*Z_ c e b f) (left-multiplication-nonnegative 0≤ef ad≤cb)) where
    0≤e : 0ℤ ≤Z e
    0≤e = bi-congruent-order _≤Z_ (symmetric-on ℤ (left-zero-on _*Z_ 0ℤ f)) (symmetric-on ℤ (right-identity-on _*Z_ e)) 0f≤e1

    e≠0 : ¬ (e =Z 0ℤ)
    e≠0 e=0 = r≠0 (q= (begin≅
            e *Z 1ℤ     ≅< right-congruent-on _*Z_ e=0 >
            0ℤ          ≅< symmetric-on ℤ (left-zero-on _*Z_ 0ℤ f) >
            0ℤ *Z f     ∎))

    0≤ef : 0ℤ ≤Z e *Z f
    0≤ef = *Z-nonnegative 0≤e 0≤f

    ef≠0 : ¬ (e *Z f =Z 0ℤ)
    ef≠0 ef=0 = f≠0 (cancel-left-multiplication-by-nonzero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ e f 0ℤ e≠0 (transitive-on ℤ ef=0 (symmetric-on ℤ (right-zero-on _*Z_ 0ℤ e))))

avg : ℚ → ℚ → ℚ
avg p q = (p + q) * 1/2ℚ

avg-self : (p : ℚ) → p ≅ avg p p
avg-self (frac p q q≠0 0≤q) = q= (begin≅
    p *Z ((q *Z q) *Z 2ℤ)       ≅< left-congruent-on _*Z_ (left-distribute-on _*Z_ _+Z_ (q *Z q) 1ℤ 1ℤ) >
    p *Z ((q *Z q) *Z 1ℤ +Z (q *Z q) *Z 1ℤ)
                                ≅< left-congruent-on _*Z_ (bi-congruent _+Z_ (right-identity-on _*Z_ (q *Z q)) (right-identity-on _*Z_ (q *Z q))) >
    p *Z (q *Z q +Z q *Z q)     ≅< left-congruent-on _*Z_ (symmetric-on ℤ (right-distribute-on _*Z_ _+Z_ q q q)) >
    p *Z ((q +Z q) *Z q)        ≅< left-associate-on _*Z_ p (q +Z q) q >
    (p *Z (q +Z q)) *Z q        ≅< right-congruent-on _*Z_ (left-distribute-on _*Z_ _+Z_ p q q) >
    (p *Z q +Z p *Z q) *Z q     ≅< right-congruent-on _*Z_ (symmetric-on ℤ (right-identity-on _*Z_ (p *Z q +Z p *Z q))) >
    ((p *Z q +Z p *Z q) *Z 1ℤ) *Z q
                                ∎)

private
    -1/2≠0ℚ : ¬ (1/2ℚ ≅ 0ℚ)
    -1/2≠0ℚ (q= (z= ()))

    2ℚ : ℚ
    2ℚ = ℤ-to-ℚ (1ℤ +Z 1ℤ)

    2≠0ℚ : ¬ (2ℚ ≅ 0ℚ)
    2≠0ℚ (q= (z= ()))

    avg-≤-right : (p q r : ℚ) → q ≤ r → avg p q ≤ avg p r
    avg-≤-right p q r q≤r = right-positive-*-≤ {p + q} {p + r} {1/2ℚ} (q≤ (z≤ 0≤)) -1/2≠0ℚ (left-+-preserves-≤ p q≤r)  

avg-commute : (p q : ℚ) → avg p q ≅ avg q p
avg-commute p q = right-congruent-on _*_ (commute-on _+_ p q)

private
    avg-≤-left : (p q r : ℚ) → p ≤ q → avg p r ≤ avg q r
    avg-≤-left p q r p≤q = bi-congruent-order _≤_ (avg-commute p r) (avg-commute q r) (avg-≤-right r p q p≤q)

avg-above-lower : (p q : ℚ) → p ≤ q → p ≤ avg p q
avg-above-lower p q p≤q = right-congruent-on-order _≤_ (symmetric-on ℚ (avg-self p)) (avg-≤-right p p q p≤q)

avg-below-higher : (p q : ℚ) → p ≤ q → avg p q ≤ q
avg-below-higher p q p≤q = left-congruent-on-order _≤_ (symmetric-on ℚ (avg-self q)) (avg-≤-left p q q p≤q)

avg-left-injective : (p : ℚ) → Injective (avg p)
avg-left-injective p {q} {r} avgpq=avgpr = begin≅
    q                       ≅< symmetric-on ℚ (right-identity-on _*_ q) >
    q * 1ℚ                  ≅< left-congruent-on _*_ (symmetric-on ℚ (recip-left-inverse 2ℚ 2≠0ℚ)) >
    q * (x * 2ℚ)            ≅< left-congruent-on _*_ {q} (right-congruent-on _*_ {2ℚ} x=1/2) >
    q * (1/2ℚ * 2ℚ)         ≅< right-congruent-on _*_ (symmetric-on ℚ (left-identity-on _+_ q)) >
    (0ℚ + q) * (1/2ℚ * 2ℚ)  ≅< right-congruent-on _*_ (right-congruent-on _+_ (symmetric-on ℚ (left-inverse-on _+_ 0ℚ neg p))) >
    ((neg p + p) + q) * (1/2ℚ * 2ℚ)
                            ≅< right-congruent-on _*_ (right-associate-on _+_ (neg p) p q) >
    (neg p + (p + q)) * (1/2ℚ * 2ℚ)
                            ≅< right-distribute-on _*_ _+_ (neg p) (p + q) (1/2ℚ * 2ℚ) >
    neg p * (1/2ℚ * 2ℚ) + (p + q) * (1/2ℚ * 2ℚ)
                            ≅< left-congruent-on _+_ (left-associate-on _*_ (p + q) 1/2ℚ 2ℚ) >
    neg p * (1/2ℚ * 2ℚ) + ((p + q) * 1/2ℚ) * 2ℚ
                            ≅< left-congruent-on _+_ (right-congruent-on _*_ avgpq=avgpr) >
    neg p * (1/2ℚ * 2ℚ) + ((p + r) * 1/2ℚ) * 2ℚ
                            ≅< left-congruent-on _+_ (right-associate-on _*_ (p + r) 1/2ℚ 2ℚ) >
    neg p * (1/2ℚ * 2ℚ) + (p + r) * (1/2ℚ * 2ℚ)
                            ≅< symmetric-on ℚ (right-distribute-on _*_ _+_ (neg p) (p + r) (1/2ℚ * 2ℚ)) >
    (neg p + (p + r)) * (1/2ℚ * 2ℚ)
                            ≅< bi-congruent _*_ (left-associate-on _+_ (neg p) p r) (right-congruent-on _*_ {2ℚ} (symmetric-on ℚ x=1/2)) >
    ((neg p + p) + r) * (x * 2ℚ)
                            ≅< bi-congruent _*_ (right-congruent-on _+_ (left-inverse-on _+_ 0ℚ neg p)) (recip-left-inverse 2ℚ 2≠0ℚ) >
    (0ℚ + r) * 1ℚ           ≅< right-identity-on _*_ (0ℚ + r) >
    0ℚ + r                  ≅< left-identity-on _+_ r >
    r                       ∎
    where   x : ℚ
            x = recip 2ℚ 2≠0ℚ

            x=1/2 : x ≅ 1/2ℚ
            x=1/2 = q= (reflexive-on ℤ (1ℤ +Z 1ℤ))

avg-right-injective : (p : ℚ) → Injective (λ q → avg q p)
avg-right-injective p {q} {r} avgqp=avgrp = avg-left-injective p (begin≅
    avg p q     ≅< avg-commute p q >
    avg q p     ≅< avgqp=avgrp >
    avg r p     ≅< avg-commute r p >
    avg p r     ∎)
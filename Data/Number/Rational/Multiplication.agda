module Data.Number.Rational.Multiplication where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Int.Base renaming (_≅_ to _=Z_; neg to negZ)
open import Data.Number.Int.Addition renaming (_+_ to _+Z_)
open import Data.Number.Int.Multiplication renaming (_*_ to _*Z_)
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
open import Data.Number.Rational.Addition
open import Structure.Algebraic.Ringoid
open import Structure.Algebraic.Field

_*_ : BinOp ℚ
frac p q q≠0 * frac r s s≠0 = frac (p *Z r) (q *Z s) qs≠0
    where   qs≠0 : ¬ (q *Z s) =Z 0ℤ
            qs≠0 qs=0 with product-is-zero-one-is-zero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ q s qs=0
            ... | left q=0  = q≠0 q=0
            ... | right s=0 = s≠0 s=0

private
    is-zero-implies-numerator-zero : {p q : ℤ} {q≠0 : ¬ (q =Z 0ℤ)} → frac p q q≠0 ≅ 0ℚ → p =Z 0ℤ
    is-zero-implies-numerator-zero {p} {q} {q≠0} (q= eq) = begin≅
        p               ≅< symmetric-on ℤ (right-identity-on _*Z_ p) >
        p *Z 1ℤ         ≅< eq >
        q *Z 0ℤ         ≅< right-zero-on _*Z_ 0ℤ q >
        0ℤ              ∎

recip : (x : ℚ) → ¬ (x ≅ 0ℚ) → ℚ
recip (frac p q q≠0) x≠0 = frac q p lemma where
    lemma : ¬ (p =Z 0ℤ)
    lemma p=0 = x≠0 (q= (begin≅
        p *Z 1ℤ         ≅< right-congruent-on _*Z_ p=0 >
        0ℤ *Z 1ℤ        ≅<>
        0ℤ              ≅< symmetric-on ℤ (right-zero-on _*Z_ 0ℤ q) >
        q *Z 0ℤ         ∎))
private
    recip-left-inverse : (x : ℚ) → (x≠0 : ¬ (x ≅ 0ℚ)) → (recip x x≠0 * x ≅ 1ℚ)
    recip-left-inverse (frac p q q≠0) x≠0 = q= (right-congruent-on _*Z_ (commute-on _*Z_ q p))

    *-left-congruent : LeftCongruent _*_
    *-left-congruent {frac p q q≠0} {frac r s s≠0} {frac t u u≠0} (q= ru=st) = q= (begin≅
        (p *Z r) *Z (q *Z u)            ≅< <ab><cd>-to-<ac><bd>-on _*Z_ p r q u >
        (p *Z q) *Z (r *Z u)            ≅< left-congruent-on _*Z_ ru=st >
        (p *Z q) *Z (s *Z t)            ≅< <ab><cd>-to-<ad><bc>-on _*Z_ p q s t >
        (p *Z t) *Z (q *Z s)            ≅< commute-on _*Z_ (p *Z t) (q *Z s) >
        (q *Z s) *Z (p *Z t)            ∎)

    *-commute : Commute _*_
    *-commute (frac p q q≠0) (frac r s s≠0) = q= (begin≅
        (p *Z r) *Z (s *Z q)    ≅< commute-on _*Z_ (p *Z r) (s *Z q) >
        (s *Z q) *Z (p *Z r)    ≅< bi-congruent _*Z_ (commute-on _*Z_ s q) (commute-on _*Z_ p r) >
        (q *Z s) *Z (r *Z p)    ∎)

instance
    *-is-commutative : IsCommutative _*_
    *-is-commutative = record {commute = *-commute}

    *-bi-congruent : BiCongruent _*_
    *-bi-congruent = bi-congruent-commutative _*_ *-left-congruent 

    *-magma : Magma _*_
    *-magma = record {}

    *-commutative-magma : CommutativeMagma _*_
    *-commutative-magma = record {}

private
    *-assoc : Associate _*_
    *-assoc (frac p q q≠0) (frac r s s≠0) (frac t u u≠0) = q= (begin≅
        (p *Z (r *Z t)) *Z ((q *Z s) *Z u)      ≅< commute-on _*Z_ (p *Z (r *Z t)) ((q *Z s) *Z u) >
        ((q *Z s) *Z u) *Z (p *Z (r *Z t))      ≅< bi-congruent _*Z_ (right-associate-on _*Z_ q s u) (left-associate-on _*Z_ p r t) >
        (q *Z (s *Z u)) *Z ((p *Z r) *Z t)      ∎)

instance
    *-is-associative : IsAssociative _*_ 
    *-is-associative = record {associate = *-assoc}

    *-semigroup : Semigroup _*_
    *-semigroup = record {}

    *-commutative-semigroup : CommutativeSemigroup _*_
    *-commutative-semigroup = record {}

private
    *-left-identity : LeftIdentity _*_ 1ℚ
    *-left-identity (frac p q q≠0) = q= (begin≅
        (1ℤ *Z p) *Z q  ≅< right-associate-on _*Z_ 1ℤ p q >
        1ℤ *Z (p *Z q)  ≅< left-congruent-on _*Z_ (commute-on _*Z_ p q) >
        1ℤ *Z (q *Z p)  ≅< left-associate-on _*Z_ 1ℤ q p >
        (1ℤ *Z q) *Z p  ∎)

instance
    *-has-identity : HasIdentity _*_ 1ℚ
    *-has-identity = has-identity-commute *-left-identity

    *-monoid : Monoid _*_ 1ℚ
    *-monoid = record {}

    *-commutative-monoid : CommutativeMonoid _*_ 1ℚ
    *-commutative-monoid = record {}

private
    *-+-left-distribute : (a b c : ℚ) → a * (b + c) ≅ (a * b) + (a * c)
    *-+-left-distribute (frac p q q≠0) (frac r s s≠0) (frac t u u≠0) = q= (begin≅
        (p *Z (r *Z u +Z t *Z s)) *Z ((q *Z s) *Z (q *Z u))         ≅< commute-on _*Z_ (p *Z (r *Z u +Z t *Z s)) ((q *Z s) *Z q *Z u) >
        ((q *Z s) *Z (q *Z u)) *Z (p *Z (r *Z u +Z t *Z s))         ≅< right-congruent-on _*Z_ (right-associate-on _*Z_ q s (q *Z u)) >
        (q *Z (s *Z (q *Z u))) *Z (p *Z (r *Z u +Z t *Z s))         ≅< <ab>c-to-b<ca>-on _*Z_ q (s *Z q *Z u) (p *Z (r *Z u +Z t *Z s)) >
        (s *Z (q *Z u)) *Z (p *Z (r *Z u +Z t *Z s)) *Z q           ≅< bi-congruent _*Z_ (a<bc>-to-b<ac>-on _*Z_ s q u) (right-congruent-on _*Z_ (left-distribute-on _*Z_ _+Z_ p (r *Z u) (t *Z s))) >
        (q *Z (s *Z u)) *Z (p *Z (r *Z u) +Z p *Z (t *Z s)) *Z q    ≅< left-congruent-on _*Z_ (right-congruent-on _*Z_ (bi-congruent _+Z_ (left-associate-on _*Z_ p r u) (left-associate-on _*Z_ p t s))) >
        (q *Z (s *Z u)) *Z ((p *Z r) *Z u +Z (p *Z t) *Z s) *Z q    ≅< left-congruent-on _*Z_ (right-distribute-on _*Z_ _+Z_ ((p *Z r) *Z u) ((p *Z t) *Z s) q) >
        (q *Z (s *Z u)) *Z (((p *Z r) *Z u) *Z q +Z ((p *Z t) *Z s) *Z q)
                                                                    ≅< left-congruent-on _*Z_ (bi-congruent _+Z_ (right-associate-on _*Z_ (p *Z r) u q) (right-associate-on _*Z_ (p *Z t) s q)) >
        (q *Z (s *Z u)) *Z ((p *Z r) *Z (u *Z q) +Z (p *Z t) *Z (s *Z q))
                                                                    ≅< left-congruent-on _*Z_ (bi-congruent _+Z_ (left-congruent-on _*Z_ (commute-on _*Z_ u q)) (left-congruent-on _*Z_ (commute-on _*Z_ s q))) >
        (q *Z (s *Z u)) *Z ((p *Z r) *Z (q *Z u) +Z (p *Z t) *Z (q *Z s))  
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
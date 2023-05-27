{-# OPTIONS --allow-unsolved-metas #-}
module Data.Number.Rational.Addition where

open import Data.Number.Int.Base renaming (_≅_ to _=Z_; neg to negZ) hiding (neg-is-congruent)
open import Data.Number.Int.Addition renaming (_+_ to _+Z_)
    hiding (+-is-commutative; +-magma; +-commutative-magma; +-bi-congruent; +-is-associative; +-semigroup; +-commutative-semigroup; +-has-identity; +-monoid; +-commutative-monoid;
            +-has-inverse; +-group; +-abelian-group)
open import Data.Number.Int.Multiplication renaming (_*_ to _*Z_)
open import Function.Binary
open import Function.Binary.Properties
open import Function.Unary.Properties
open import Relation
open import Data.Either
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Ring
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
open import Structure.Algebraic.Ringoid
open import Structure.Algebraic.Group
open import Structure.Algebraic.Group.Abelian

_+_ : BinOp ℚ
frac p q q≠0 + frac r s s≠0 = frac (p *Z s +Z r *Z q) (q *Z s) qs≠0
    where   qs≠0 : ¬ (q *Z s) =Z 0ℤ
            qs≠0 qs=0 with product-is-zero-one-is-zero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ q s qs=0
            ... | left q=0  = q≠0 q=0
            ... | right s=0 = s≠0 s=0

neg : ℚ → ℚ
neg (frac p q q≠0) = frac (negZ p) q q≠0

private
    +-left-congruent : LeftCongruent _+_
    +-left-congruent {frac p q q≠0} {frac r s s≠0} {frac t u u≠0} (q= ru=st) = q= (begin≅
        (p *Z s +Z r *Z q) *Z (q *Z u)                  ≅< right-distribute-on _*Z_ _+Z_ (p *Z s) (r *Z q) (q *Z u) >
        (p *Z s) *Z (q *Z u) +Z (r *Z q) *Z (q *Z u)    ≅< left-congruent-on _+Z_ (<ab><cd>-to-<ad><bc>-on _*Z_ r q q u) >
        (p *Z s) *Z (q *Z u) +Z (r *Z u) *Z (q *Z q)    ≅< left-congruent-on _+Z_ (right-congruent-on _*Z_ ru=st) >
        (p *Z s) *Z (q *Z u) +Z (s *Z t) *Z (q *Z q)    ≅< bi-congruent _+Z_ (<ab><cd>-to-<cb><ad>-on _*Z_ p s q u) (<ab><cd>-to-<ad><bc>-on _*Z_ s t q q) >
        (q *Z s) *Z (p *Z u) +Z (s *Z q) *Z (t *Z q)    ≅< left-congruent-on _+Z_ (right-congruent-on _*Z_ (commute-on _*Z_ s q)) >
        (q *Z s) *Z (p *Z u) +Z (q *Z s) *Z (t *Z q)    ≅< symmetric-on ℤ (left-distribute-on _*Z_ _+Z_ (q *Z s) (p *Z u) (t *Z q)) >
        (q *Z s) *Z (p *Z u +Z t *Z q)                  ∎)
    
    +-commute : Commute _+_
    +-commute (frac p q q≠0) (frac r s s≠0) = q= (begin≅
        (p *Z s +Z r *Z q) *Z (s *Z q)      ≅< commute-on _*Z_ (p *Z s +Z r *Z q) (s *Z q) >
        (s *Z q) *Z (p *Z s +Z r *Z q)      ≅< bi-congruent _*Z_ (commute-on _*Z_ s q) (commute-on _+Z_ (p *Z s) (r *Z q)) >
        (q *Z s) *Z (r *Z q +Z p *Z s)      ∎)

instance
    +-is-commutative : IsCommutative _+_
    +-is-commutative = record {commute = +-commute}

    +-bi-congruent : BiCongruent _+_
    +-bi-congruent = bi-congruent-commutative _+_ +-left-congruent

    +-magma : Magma _+_
    +-magma = record {}

    +-commutative-magma : CommutativeMagma _+_
    +-commutative-magma = record {}

private
    +-assoc : Associate _+_
    +-assoc (frac p q q≠0) (frac r s s≠0) (frac t u u≠0) = q= (begin≅
        (p *Z (s *Z u) +Z (r *Z u +Z t *Z s) *Z q) *Z ((q *Z s) *Z u)           ≅< commute-on _*Z_ (p *Z (s *Z u) +Z (r *Z u +Z t *Z s) *Z q) ((q *Z s) *Z u) >
        ((q *Z s) *Z u) *Z (p *Z (s *Z u) +Z (r *Z u +Z t *Z s) *Z q)           ≅< bi-congruent _*Z_ (right-associate-on _*Z_ q s u)
                                                                                        (bi-congruent _+Z_ (left-associate-on _*Z_ p s u) (right-distribute-on _*Z_ _+Z_ (r *Z u) (t *Z s) q)) >
        (q *Z (s *Z u)) *Z ((p *Z s) *Z u +Z ((r *Z u) *Z q +Z (t *Z s) *Z q))  ≅< left-congruent-on _*Z_ (left-associate-on _+Z_ ((p *Z s) *Z u) ((r *Z u) *Z q) ((t *Z s) *Z q)) >
        (q *Z (s *Z u)) *Z (((p *Z s) *Z u +Z (r *Z u) *Z q) +Z (t *Z s) *Z q)  ≅< left-congruent-on _*Z_
                                                                                        (bi-congruent _+Z_
                                                                                            (left-congruent-on _+Z_ (<ab>c-to-<ac>b-on _*Z_ r u q))
                                                                                            (<ab>c-to-a<cb>-on _*Z_ t s q)) >
        (q *Z (s *Z u)) *Z (((p *Z s) *Z u +Z (r *Z q) *Z u) +Z t *Z (q *Z s))  ≅< left-congruent-on _*Z_
                                                                                        (right-congruent-on _+Z_
                                                                                            (symmetric-on ℤ
                                                                                                (right-distribute-on _*Z_ _+Z_ (p *Z s) (r *Z q) u))) >
        (q *Z (s *Z u)) *Z (((p *Z s +Z r *Z q) *Z u) +Z t *Z (q *Z s))         ∎)

instance
    +-is-associative : IsAssociative _+_
    +-is-associative = record {associate = +-assoc}

    +-semigroup : Semigroup _+_
    +-semigroup = record {}

    +-commutative-semigroup : CommutativeSemigroup _+_
    +-commutative-semigroup = record {}

private
    +-left-identity : LeftIdentity _+_ 0ℚ
    +-left-identity (frac p q q≠0) = q= (begin≅
        (0ℤ *Z q +Z p *Z 1ℤ) *Z q       ≅< right-congruent-on _*Z_ (right-congruent-on _+Z_ (left-zero-on _*Z_ 0ℤ q)) >
        (0ℤ +Z p *Z 1ℤ) *Z q            ≅< right-congruent-on _*Z_ (left-identity-on _+Z_ (p *Z 1ℤ)) >
        (p *Z 1ℤ) *Z q                  ≅< <ab>c-to-<bc>a-on _*Z_ p 1ℤ q >
        (1ℤ *Z q) *Z p                  ∎)

instance
    +-has-identity : HasIdentity _+_ 0ℚ
    +-has-identity = has-identity-commute +-left-identity

    +-monoid : Monoid _+_ 0ℚ
    +-monoid = record {}

    +-commutative-monoid : CommutativeMonoid _+_ 0ℚ
    +-commutative-monoid = record {}

private
    neg-congruent : Congruent neg
    neg-congruent {frac p q q≠0} {frac r s s≠0} (q= ps=qr) = q= (begin≅
        negZ p *Z s         ≅< left-times-neg-on _*Z_ _+Z_ 1ℤ 0ℤ negZ p s >
        negZ (p *Z s)       ≅< congruent-on negZ ps=qr >
        negZ (q *Z r)       ≅< symmetric-on ℤ (right-times-neg-on _*Z_ _+Z_ 1ℤ 0ℤ negZ q r) >
        q *Z negZ r         ∎)

    +-left-inverse : LeftInverse _+_ 0ℚ neg
    +-left-inverse (frac p q q≠0) = q= (begin≅
        (negZ p *Z q +Z p *Z q) *Z 1ℤ   ≅< right-identity-on _*Z_ (negZ p *Z q +Z p *Z q) >
        negZ p *Z q +Z p *Z q           ≅< symmetric-on ℤ (right-distribute-on _*Z_ _+Z_ (negZ p) p q) >
        (negZ p +Z p) *Z q              ≅< right-congruent-on _*Z_ (left-inverse-on _+Z_ 0ℤ negZ p) >
        0ℤ *Z q                         ≅< left-zero-on _*Z_ 0ℤ q >
        0ℤ                              ≅< symmetric-on ℤ (right-zero-on _*Z_ 0ℤ (q *Z q)) >
        (q *Z q) *Z 0ℤ                  ∎)

instance
    neg-is-congruent : IsCongruent neg
    neg-is-congruent = record { congruent = neg-congruent }
    
    +-has-inverse : HasInverse _+_ 0ℚ neg
    +-has-inverse = has-inverse-commute +-left-inverse

    +-group : Group _+_ 0ℚ neg
    +-group = record {}

    +-abelian-group : AbelianGroup _+_ 0ℚ neg
    +-abelian-group = record {}
module Data.Number.Rational.Order where

open import Agda.Primitive
open import Relation
open import Data.Number.Rational
open import Data.Number.Int.Base renaming (_≅_ to _=Z_; neg to negZ)
open import Data.Number.Int.Addition renaming (_+_ to _+Z_)
open import Data.Number.Int.Multiplication renaming (_*_ to _*Z_)
open import Data.Number.Int.Order renaming (_≤_ to _≤Z_) hiding (≤-is-reflexive; ≤-is-transitive; ≤-pre-order; ≤-partial-order; ≤-is-antisymmetric; ≤-total-order)
open import Logic
open import Relation.Properties
open import Relation.Order.Partial
open import Relation.Order.Total
open import Data.Either
open import Structure.Setoid
open import Structure.Algebraic.Ring
open import Structure.Algebraic.IntegralDomain
open import Structure.Setoid.Equation
open import Function.Binary.Properties
open import Structure.Algebraic.Semigroup.Commutative
open import Data.Number.Nat using (0≤)

data _≤_ : Rel lzero ℚ where
    q≤ : {p q r s : ℤ} {q≠0 : ¬ (q =Z 0ℤ)} {0≤q : 0ℤ ≤Z q} {s≠0 : ¬ (s =Z 0ℤ)} {0≤s : 0ℤ ≤Z s} → (p *Z s) ≤Z (r *Z q) → frac p q q≠0 0≤q ≤ frac r s s≠0 0≤s

infix 7 _≤_

0≰-1ℚ : ¬ (0ℚ ≤ -1ℚ)
0≰-1ℚ (q≤ (z≤ ()))

-1≤0ℚ : -1ℚ ≤ 0ℚ
-1≤0ℚ = q≤ (z≤ 0≤)

private
    *Z-nonnegative : {x y : ℤ} → 0ℤ ≤Z x → 0ℤ ≤Z y → 0ℤ ≤Z (x *Z y)
    *Z-nonnegative {x} 0≤x 0≤y = right-congruent-on-order _≤Z_ (right-zero-on _*Z_ 0ℤ x) (left-multiplication-nonnegative 0≤x 0≤y)

    *Z-negative-nonnegative : {x y : ℤ} → x ≤Z 0ℤ → 0ℤ ≤Z y → (x *Z y) ≤Z 0ℤ
    *Z-negative-nonnegative {x} x≤0 0≤y = left-congruent-on-order _≤Z_ (right-zero-on _*Z_ 0ℤ x) (left-multiplication-negative x≤0 0≤y)

    ≤-reflexive : Reflexive _≤_
    ≤-reflexive (frac p q q≠0 0≤q) = q≤ (reflexive-order-on _≤Z_ (p *Z q))

    ≤-antisymmetric : Antisymmetric _≤_
    ≤-antisymmetric (q≤ cmp1) (q≤ cmp2) = q= (antisymmetric-order-on _≤Z_ cmp1 cmp2)

    ≤-transitive : Transitive _≤_
    ≤-transitive {frac p q q≠0 0≤q} {frac r s s≠0 0≤s} {frac t u u≠0 0≤u} (q≤ ps≤rq) (q≤ ru≤ts) with trichotomy-on _≤Z_ r 0ℤ
    ... | triE r=0  = q≤ (transitive-order-on _≤Z_ pu≤0 0≤tq) where
            rx=0 : (x : ℤ) → r *Z x =Z 0ℤ
            rx=0 x = begin≅
                r *Z x      ≅< right-congruent-on _*Z_ r=0 >
                0ℤ *Z x     ≅< left-zero-on _*Z_ 0ℤ x >
                0ℤ          ∎

            ps≤0 : p *Z s ≤Z 0ℤ
            ps≤0 = left-congruent-on-order _≤Z_ (rx=0 q) ps≤rq

            p≤0 : p ≤Z 0ℤ
            p≤0 = cancel-right-multiplication-positive-≤ p 0ℤ s 0≤s s≠0 (left-congruent-on-order _≤Z_ (symmetric-on ℤ (left-zero-on _*Z_ 0ℤ s)) ps≤0)

            0≤ts : 0ℤ ≤Z t *Z s
            0≤ts = right-congruent-on-order _≤Z_ (rx=0 u) ru≤ts

            0≤t : 0ℤ ≤Z t
            0≤t = cancel-right-multiplication-positive-≤ 0ℤ t s 0≤s s≠0 (right-congruent-on-order _≤Z_ (symmetric-on ℤ (left-zero-on _*Z_ 0ℤ s)) 0≤ts)

            0≤tq : 0ℤ ≤Z t *Z q
            0≤tq = right-congruent-on-order _≤Z_ (left-zero-on _*Z_ 0ℤ q) (right-multiplication-nonnegative 0≤q 0≤t)

            pu≤0 : p *Z u ≤Z 0ℤ
            pu≤0 = left-congruent-on-order _≤Z_ (left-zero-on _*Z_ 0ℤ u) (right-multiplication-nonnegative 0≤u p≤0)
    ... | triG _ r≠0 0≤r = q≤ (cancel-left-multiplication-positive-≤ (r *Z s) (p *Z u) (t *Z q) (*Z-nonnegative 0≤r 0≤s) rs≠0 
                (bi-congruent-order _≤Z_  (<ab><cd>-to-<cb><ad>-on _*Z_ r s p u) (<ab><cd>-to-<ad><cb>-on _*Z_ r s t q) psru≤rqts)) where
            rs≠0 : ¬ (r *Z s =Z 0ℤ)
            rs≠0 rs=0 = s≠0 (cancel-left-multiplication-by-nonzero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ r s 0ℤ r≠0 (transitive-on ℤ rs=0 (symmetric-on ℤ (right-zero-on _*Z_ 0ℤ r))))

            psru≤rqru : (p *Z s) *Z (r *Z u) ≤Z (r *Z q) *Z (r *Z u)
            psru≤rqru = right-multiplication-nonnegative (*Z-nonnegative 0≤r 0≤u) ps≤rq

            rqru≤rqts : (r *Z q) *Z (r *Z u) ≤Z (r *Z q) *Z (t *Z s)
            rqru≤rqts = left-multiplication-nonnegative (*Z-nonnegative 0≤r 0≤q) ru≤ts

            psru≤rqts = transitive-order-on _≤Z_ psru≤rqru rqru≤rqts
    ... | triL r≤0 r≠0 _ = q≤ (cancel-left-multiplication-negative-≤ (r *Z s) (t *Z q) (p *Z u) rs≤0 rs≠0 
                (bi-congruent-order _≤Z_ (<ab><cd>-to-<ad><cb>-on _*Z_ r s t q) (<ab><cd>-to-<cb><ad>-on _*Z_ r s p u) (transitive-order-on _≤Z_ rqts≤rqru rqru≤psru))) where
            rs≤0 : r *Z s ≤Z 0ℤ
            rs≤0 = *Z-negative-nonnegative r≤0 0≤s
            
            rs≠0 : ¬ (r *Z s =Z 0ℤ)
            rs≠0 rs=0 = s≠0 (cancel-left-multiplication-by-nonzero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ r s 0ℤ r≠0 (transitive-on ℤ rs=0 (symmetric-on ℤ (right-zero-on _*Z_ 0ℤ r))))

            rqts≤rqru : (r *Z q) *Z (t *Z s) ≤Z (r *Z q) *Z (r *Z u)
            rqts≤rqru = left-multiplication-negative (*Z-negative-nonnegative r≤0 0≤q) ru≤ts

            rqru≤psru : (r *Z q) *Z (r *Z u) ≤Z (p *Z s) *Z (r *Z u)
            rqru≤psru = right-multiplication-negative (*Z-negative-nonnegative r≤0 0≤u) ps≤rq

    ≤-reflexive-equiv : {p q : ℚ} → p ≅ q → p ≤ q
    ≤-reflexive-equiv (q= eq) = q≤ (reflexive-equiv-order-on _≤Z_ eq)

    ≤-trichotomy : (x y : ℚ) → Tri _≅_ _≤_ x y
    ≤-trichotomy (frac p q q≠0 0≤q) (frac r s s≠0 0≤s) with trichotomy-on _≤Z_ (p *Z s) (r *Z q)
    ... | triE ps=rq    = triE (q= ps=rq)
    ... | triL ps<rq ps≠rq ps≯rq = triL (q≤ ps<rq) x≠y x≯y where
            x≠y : ¬ (frac p q q≠0 0≤q ≅ frac r s s≠0 0≤s)
            x≠y (q= ps=rq) = ps≠rq ps=rq

            x≯y : ¬ (frac r s s≠0 0≤s ≤ frac p q q≠0 0≤q)
            x≯y (q≤ rs≤pq) = ps≯rq (rs≤pq)
    ... | triG ps≮rq ps≠rq rq≤ps = triG x≮y x≠y (q≤ rq≤ps) where
            x≠y : ¬ (frac p q q≠0 0≤q ≅ frac r s s≠0 0≤s)
            x≠y (q= ps=rq) = ps≠rq ps=rq

            x≮y : ¬ (frac p q q≠0 0≤q ≤ frac r s s≠0 0≤s)
            x≮y (q≤ ps≤rq) = ps≮rq ps≤rq

instance
    ≤-is-reflexive : IsReflexive _≤_
    ≤-is-reflexive = record {reflexive = ≤-reflexive}

    ≤-is-transitive : IsTransitive _≤_
    ≤-is-transitive = record {transitive = ≤-transitive}

    ≤-pre-order : PreOrder _≤_
    ≤-pre-order = record {}

    ≤-is-antisymmetric : IsAntisymmetric _≤_
    ≤-is-antisymmetric = record {antisymmetric = ≤-antisymmetric}

    ≤-partial-order : PartialOrder _≤_
    ≤-partial-order = record {reflexive-equiv = ≤-reflexive-equiv}

    ≤-total-order : TotalOrder _≤_
    ≤-total-order = record {trichotomy = ≤-trichotomy}
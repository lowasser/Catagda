module Data.Number.Real.Dedekind where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Bool
open import Relation
open import Relation.Properties
open import Relation.Equivalence.Structural
open import Data.Number.Rational renaming (_≅_ to _=Q_)
open import Data.Number.Rational.Addition renaming (_+_ to _+Q_; neg to negQ)
open import Data.Number.Rational.Order renaming (_≤_ to _≤Q_) hiding (≤-is-reflexive; ≤-pre-order; ≤-is-transitive; ≤-partial-order; ≤-is-antisymmetric)
open import Data.Number.Rational.Multiplication renaming (_*_ to _*Q)
open import Logic
open import Structure.Setoid
open import Relation.Order.Total
open import Structure.Setoid.Equation
open import Function.Binary.Properties
open import Relation.Order.Partial

record ℝ : Set where
    field
        is-less : ℚ → Bool
        lower-bound upper-bound : ℚ
        lower-bound-is : is-less lower-bound ≡ true
        upper-bound-is : is-less upper-bound ≡ false

        is-less-closed-downward : (p q : ℚ) → p ≤Q q → is-less q ≡ true → is-less p ≡ true
        no-greatest-less : (p : ℚ) → is-less p ≡ true → Σ ℚ (λ q → ¬ (p =Q q) ∧ p ≤Q q ∧ is-less q ≡ true)

open ℝ

data _≤_ : Rel lzero ℝ where
    r≤ : (x y : ℝ) → ((q : ℚ) → ℝ.is-less x q ≡ true → ℝ.is-less y q ≡ true) → x ≤ y

data _≅_ : Rel lzero ℝ where
    r= : {x y : ℝ} → x ≤ y → y ≤ x → x ≅ y

private
    ≤-reflexive : Reflexive _≤_
    ≤-reflexive x = r≤ x x λ _ eq → eq

    ≤-transitive : Transitive _≤_
    ≤-transitive (r≤ x y <x→<y) (r≤ y z <y→<z) = r≤ x z λ q eq → <y→<z q (<x→<y q eq)

    ≅-reflexive : Reflexive _≅_
    ≅-reflexive x = r= (≤-reflexive x) (≤-reflexive x)

    ≅-symmetric : Symmetric _≅_
    ≅-symmetric (r= x≤y y≤x) = r= y≤x x≤y

    ≅-transitive : Transitive _≅_
    ≅-transitive (r= x≤y y≤x) (r= y≤z z≤y) = r= (≤-transitive x≤y y≤z) (≤-transitive z≤y y≤x)

instance
    ℝ-setoid : Setoid lzero ℝ
    ℝ-setoid = make-setoid _≅_ ≅-reflexive ≅-transitive ≅-symmetric

ℚ-to-ℝ : ℚ → ℝ
ℚ-to-ℝ q = record {
        is-less = less; 
        upper-bound = q;
        upper-bound-is = upper-bound-is-q; 
        lower-bound = q +Q -1ℚ; 
        lower-bound-is = lower-bound-is-q;
        is-less-closed-downward = is-less-closed-downward-q;
        no-greatest-less = λ p eq → avg p q , no-greatest-less-neq p eq , p≤avgpq p eq , avgpq<p p eq
        } where
    less : ℚ → Bool
    less p with trichotomy-on _≤Q_ p q
    ... | triL _ _ _ = true
    ... | triE _    = false
    ... | triG _ _ _ = false

    upper-bound-is-q : less q ≡ false
    upper-bound-is-q with trichotomy-on _≤Q_ q q
    ... | triL _ q≠q _ = contradiction-implies-anything (q≠q (reflexive-on ℚ q))
    ... | triE _ = refl
    ... | triG _ q≠q _ = contradiction-implies-anything (q≠q (reflexive-on ℚ q))

    lower-bound-is-q : less (q +Q -1ℚ) ≡ true
    lower-bound-is-q with trichotomy-on _≤Q_ (q +Q -1ℚ) q
    ... | triL _ _ _ = refl
    ... | triE q-1=q = contradiction-implies-anything (-1≠0ℚ (begin≅ 
            -1ℚ                     ≅< symmetric-on ℚ (left-identity-on _+Q_ -1ℚ) >
            0ℚ +Q -1ℚ               ≅< right-congruent-on _+Q_ (symmetric-on ℚ (left-inverse-on _+Q_ 0ℚ negQ q)) >
            (negQ q +Q q) +Q -1ℚ    ≅< right-associate-on _+Q_ (negQ q) q -1ℚ >
            negQ q +Q (q +Q -1ℚ)    ≅< left-congruent-on _+Q_ q-1=q >
            negQ q +Q q             ≅< left-inverse-on _+Q_ 0ℚ negQ q >
            0ℚ                      ∎))
    ... | triG _ _ q≤q-1 = contradiction-implies-anything (0≰-1ℚ 
            (bi-congruent-order _≤Q_ 
                (symmetric-on ℚ (left-inverse-on _+Q_ 0ℚ negQ q)) 
                (symmetric-on ℚ (begin≅
                    negQ q +Q (q +Q -1ℚ)    ≅< left-associate-on _+Q_ (negQ q) q -1ℚ >
                    (negQ q +Q q) +Q -1ℚ    ≅< right-congruent-on _+Q_ (left-inverse-on _+Q_ 0ℚ negQ q) >
                    0ℚ +Q -1ℚ               ≅< left-identity-on _+Q_ -1ℚ >
                    -1ℚ                     ∎)) 
                (left-+-preserves-≤ (negQ q) q≤q-1)))

    is-less-closed-downward-q : (r s : ℚ) → r ≤Q s → less s ≡ true → less r ≡ true
    is-less-closed-downward-q r s r≤s eq with trichotomy-on _≤Q_ r q | trichotomy-on _≤Q_ s q | eq
    ... | triL _ _ _ | triL _ _ _ | refl            = refl
    ... | triE r=q | triL s≤q s≠q _ | refl          = contradiction-implies-anything (s≠q (between-equal-on _≤Q_ r≤s s≤q r=q))
    ... | triG _ r≠q q≤r | triL s≤q _ _ | refl      = contradiction-implies-anything (r≠q (antisymmetric-order-on _≤Q_ (transitive-order-on _≤Q_ r≤s s≤q) q≤r))

    no-greatest-less-neq : (p : ℚ) → less p ≡ true → ¬ (p =Q avg p q)
    no-greatest-less-neq p eq p=avgpq with trichotomy-on _≤Q_ p q | eq
    ... | triL _ p≠q _ | refl = p≠q (avg-left-injective p (begin≅
            avg p p     ≅< symmetric-on ℚ (avg-self p) >
            p           ≅< p=avgpq >
            avg p q     ∎))

    p≤avgpq : (p : ℚ) → less p ≡ true → p ≤Q avg p q
    p≤avgpq p eq with trichotomy-on _≤Q_ p q | eq
    ... | triL p≤q _ _ | refl = avg-above-lower p q p≤q

    avgpq<p : (p : ℚ) → less p ≡ true → less (avg p q) ≡ true
    avgpq<p p eq with trichotomy-on _≤Q_ p q | eq | trichotomy-on _≤Q_ (avg p q) q
    ... | triL _ _ _ | refl | triL _ _ _ = refl
    ... | triL _ p≠q _ | refl | triE avgpq=q = contradiction-implies-anything (p≠q (avg-right-injective q (begin≅
            avg p q     ≅< avgpq=q >
            q           ≅< avg-self q >
            avg q q     ∎)))
    ... | triL p≤q p≠q _ | refl | triG _ q≠avgpq q≤avgpq = contradiction-implies-anything (q≠avgpq (antisymmetric-order-on _≤Q_ (avg-below-higher p q p≤q) q≤avgpq))

instance
    ≤-is-reflexive : IsReflexive _≤_
    ≤-is-reflexive = record {reflexive = ≤-reflexive}

    ≤-is-transitive : IsTransitive _≤_ 
    ≤-is-transitive = record {transitive = ≤-transitive}

    ≤-is-antisymmetric : IsAntisymmetric _≤_
    ≤-is-antisymmetric = record {antisymmetric = r=}

    ≤-pre-order : PreOrder _≤_
    ≤-pre-order = record {}

    ≤-partial-order : PartialOrder _≤_
    ≤-partial-order = record {reflexive-equiv = ≤-reflexive-equiv} where
        ≤-reflexive-equiv : {p q : ℝ} → p ≅ q → p ≤ q
        ≤-reflexive-equiv (r= p≤q _) = p≤q
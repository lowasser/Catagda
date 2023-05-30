module Data.Number.Rational.Order where

open import Agda.Primitive
open import Relation
open import Data.Number.Rational
open import Data.Number.Int.Base renaming (_≅_ to _=Z_)
open import Data.Number.Int.Addition renaming (_+_ to _+Z_)
open import Data.Number.Int.Multiplication renaming (_*_ to _*Z_)
open import Data.Number.Int.Order renaming (_≤_ to _≤Z_)
open import Logic
open import Relation.Properties
open import Relation.Order.Partial
open import Relation.Order.Total
open import Data.Either
open import Structure.Setoid
open import Structure.Algebraic.Ring

normalized-numerator : ℚ → ℤ
normalized-numerator (frac p q _) with compare-order-on _≤Z_ 0ℤ q 
... | left _    = p
... | right _   = neg p

normalized-denominator : ℚ → ℤ
normalized-denominator (frac p q _) with compare-order-on _≤Z_ 0ℤ q
... | left _    = q
... | right _   = neg q

data _≤_ : Rel lzero ℚ where
    q≤ : {p q : ℚ} → (normalized-numerator p *Z normalized-denominator q) ≤Z (normalized-numerator q *Z normalized-denominator p) → p ≤ q

private
    ≤-reflexive : Reflexive _≤_
    ≤-reflexive q = q≤ (reflexive-order-on _≤Z_ (normalized-numerator q *Z normalized-denominator q))

    normalized-product-same-as-real-product : (a b : ℤ) → (b≠0 : ¬ (b =Z 0ℤ)) → normalized-numerator (frac a b b≠0) *Z normalized-denominator (frac a b b≠0) =Z a *Z b
    normalized-product-same-as-real-product a b _ with compare-order-on _≤Z_ 0ℤ b
    ... | left _    = reflexive-on ℤ (a *Z b)
    ... | right _   = neg-times-neg-on _*Z_ _+Z_ 1ℤ 0ℤ neg a b
module Definitions.Int where

open import Agda.Primitive
open import Definitions.Nat renaming (_≤_ to _≤ℕ_)
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Equivalence 
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence.Structural.Properties(ℕ)
open import Definitions.Nat.Addition renaming (_+_ to _+ℕ_)
open import Definitions.Nat.Addition.Properties
open import Definitions.Setoid
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid.Equation
open import Definitions.Relation.Order.Pre
open import Definitions.Relation.Order.Partial

open Setoid {{ ... }}
open Equivalence {{...}}
open IsReflexive {{...}}
open IsCommutative {{...}}
open IsSymmetric {{...}}

data ℤ : Set where
    ℤ<_,_> : ℕ → ℕ → ℤ

infix 10 ℤ<_,_>

ℕ→ℤ : ℕ → ℤ
ℕ→ℤ n = ℤ< n , 0 >

0ℤ : ℤ
0ℤ = ℕ→ℤ 0

1ℤ : ℤ
1ℤ = ℕ→ℤ 1

-_ : ℤ → ℤ
- (ℤ< a , b >) = ℤ< b , a >

-1ℤ : ℤ
-1ℤ = - 1ℤ

data _ℤ≈_ : Relation ℤ where
    zeq : {a1 b1 a2 b2 : ℕ} → (a1 +ℕ b2) ≈ (a2 +ℕ b1) → ℤ< a1 , b1 > ℤ≈ ℤ< a2 , b2 >
infix 4 _ℤ≈_

data _≤_ : Relation ℤ where
    z≤ : {a1 b1 a2 b2 : ℕ} → (a1 +ℕ b2) ≤ℕ (a2 +ℕ b1) → ℤ< a1 , b1 > ≤ ℤ< a2 , b2 >

private
    ℤ≈-reflexive : Reflexive _ℤ≈_
    ℤ≈-reflexive ℤ< x , y > = zeq refl

    ℤ≈-symmetric : Symmetric _ℤ≈_
    ℤ≈-symmetric (zeq a1b2≈a2b1) = zeq (symmetric-on ℕ a1b2≈a2b1)

    ℤ≈-transitive : Transitive _ℤ≈_
    ℤ≈-transitive (zeq {ax} {bx} {ay} {by} axby≡aybx) (zeq {ay} {by} {az} {bz} aybz≡azby) = zeq (
        +ℕ-right-injective by (begin≈
            (ax +ℕ bz) +ℕ by    ≈< symmetric-on ℕ (associate-on _+ℕ_ ax bz by) >
            ax +ℕ (bz +ℕ by)    ≈< left-congruent-on _+ℕ_ {ax} (commute-on _+ℕ_ bz by) >
            ax +ℕ (by +ℕ bz)    ≈< associate-on _+ℕ_ ax by bz >
            (ax +ℕ by) +ℕ bz    ≈< right-congruent-on _+ℕ_ axby≡aybx >
            (ay +ℕ bx) +ℕ bz    ≈< right-congruent-on _+ℕ_ (commute-on _+ℕ_ ay bx) >
            (bx +ℕ ay) +ℕ bz    ≈< symmetric-on ℕ (associate-on _+ℕ_ bx ay bz) >
            bx +ℕ (ay +ℕ bz)    ≈< left-congruent-on _+ℕ_ {bx} aybz≡azby >
            bx +ℕ (az +ℕ by)    ≈< associate-on _+ℕ_ bx az by >
            (bx +ℕ az) +ℕ by    ≈< right-congruent-on _+ℕ_ (commute-on _+ℕ_ bx az) >
            (az +ℕ bx) +ℕ by    ∎))

    ≤-reflexive : Reflexive _≤_
    ≤-reflexive (ℤ< a , b >) = z≤ (reflexive-order-on _≤ℕ_ (a +ℕ b))

instance
    ℤ≈-IsReflexive : IsReflexive _ℤ≈_
    ℤ≈-IsReflexive = record { reflexive = ℤ≈-reflexive }

    ℤ≈-IsTransitive : IsTransitive _ℤ≈_
    ℤ≈-IsTransitive = record { transitive = ℤ≈-transitive }

    ℤ≈-PreOrder : PreOrder _ℤ≈_
    ℤ≈-PreOrder = record {}

    ℤ≈-IsSymmetric : IsSymmetric _ℤ≈_
    ℤ≈-IsSymmetric = record { symmetric = ℤ≈-symmetric }

    ℤ≈-Equivalence : Equivalence _ℤ≈_
    ℤ≈-Equivalence = record {}

    ℤ-Setoid : Setoid ℤ
    ℤ-Setoid = record { _≈_ = _ℤ≈_ }

    -- TODO : ≤ is a total order
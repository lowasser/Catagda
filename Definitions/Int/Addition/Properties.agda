module Definitions.Int.Addition.Properties where

open import Agda.Primitive
open import Definitions.Nat
open import Definitions.Int
open import Definitions.Int.Addition
open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Relation.Equivalence 
open import Definitions.Relation.Equivalence.Structural
open import Definitions.Relation.Equivalence.Structural.Properties(ℕ)
open import Definitions.Nat.Addition renaming (_+_ to _+ℕ_)
open import Definitions.Nat.Addition.Properties
open import Definitions.Setoid
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Setoid.Equation
open import Definitions.Magma
open import Definitions.Magma.Commutative
open import Definitions.Semigroup
open import Definitions.Semigroup.Commutative
open import Definitions.Monoid
open import Definitions.Monoid.Commutative
open import Definitions.Group
open import Definitions.Group.Abelian

open Setoid {{ ... }}
open Equivalence {{...}}
open IsReflexive {{...}}
open IsCommutative {{...}}
open IsSymmetric {{...}}

private
    +-commute : Commute _+_
    +-commute ℤ< a , b > ℤ< c , d > = zeq (begin≈
        (a +ℕ c) +ℕ (d +ℕ b)    ≈< ≡-congruent (_+ℕ (d +ℕ b)) _≡_ (commute-on _+ℕ_ a c) >
        (c +ℕ a) +ℕ (d +ℕ b)    ≈< ≡-congruent ((c +ℕ a) +ℕ_) _≡_ (commute-on _+ℕ_ d b) >
        (c +ℕ a) +ℕ (b +ℕ d)    ∎)
 
    +-cong2 : Congruent2 _+_
    +-cong2 {ℤ< ay , by >} (zeq {ax1} {bx1} {ax2} {bx2} ax1bx2≡ax2bx1) = zeq (begin≈
        (ay +ℕ ax1) +ℕ (by +ℕ bx2)  ≈< ≡-congruent ((ay +ℕ ax1) +ℕ_) _≡_ (commute-on _+ℕ_ by bx2) >
        (ay +ℕ ax1) +ℕ (bx2 +ℕ by)  ≈< symmetric-on ℕ (associate-on _+ℕ_ ay ax1 (bx2 +ℕ by)) >
        ay +ℕ (ax1 +ℕ (bx2 +ℕ by))  ≈< ≡-congruent (ay +ℕ_) _≡_ (associate-on _+ℕ_ ax1 bx2 by) >
        ay +ℕ ((ax1 +ℕ bx2) +ℕ by)  ≈< ≡-congruent (ay +ℕ_) _≡_ (≡-congruent (_+ℕ by) _≡_ ax1bx2≡ax2bx1) >
        ay +ℕ ((ax2 +ℕ bx1) +ℕ by)  ≈< ≡-congruent (ay +ℕ_) _≡_ (symmetric-on ℕ (associate-on _+ℕ_ ax2 bx1 by)) >
        ay +ℕ (ax2 +ℕ (bx1 +ℕ by))  ≈< associate-on _+ℕ_ ay ax2 (bx1 +ℕ by) >
        (ay +ℕ ax2) +ℕ (bx1 +ℕ by)  ≈< ≡-congruent ((ay +ℕ ax2) +ℕ_) _≡_ (commute-on _+ℕ_ bx1 by) >
        (ay +ℕ ax2) +ℕ (by +ℕ bx1)  ∎)

    +-cong1 : Congruent1 _+_
    +-cong1 {y} {x1} {x2} x1≈x2 = begin≈
        x1 + y      ≈< +-commute x1 y >
        y + x1      ≈< +-cong2 x1≈x2 >
        y + x2      ≈< +-commute y x2 >
        x2 + y      ∎

    +-assoc : Associate _+_
    +-assoc (ℤ< ax , bx >) (ℤ< ay , by >) (ℤ< az , bz >) = zeq (begin≈
        (ax +ℕ (ay +ℕ az)) +ℕ ((bx +ℕ by) +ℕ bz)    ≈< ≡-congruent (_+ℕ ((bx +ℕ by) +ℕ bz)) _≡_ (associate-on _+ℕ_ ax ay az) >
        ((ax +ℕ ay) +ℕ az) +ℕ ((bx +ℕ by) +ℕ bz)    ≈< ≡-congruent (((ax +ℕ ay) +ℕ az) +ℕ_) _≡_ (symmetric-on ℕ (associate-on _+ℕ_ bx by bz)) >
        ((ax +ℕ ay) +ℕ az) +ℕ (bx +ℕ (by +ℕ bz))    ∎)

    +-leftId : LeftIdentity _+_ 0ℤ
    +-leftId (ℤ< a , b >) = zeq (begin≈
        (0 +ℕ a) +ℕ b       ≈< ≡-congruent (_+ℕ b) _≡_ (left-id-on _+ℕ_ a) >
        a +ℕ b              ≈< ≡-congruent (a +ℕ_) _≡_ (symmetric-on ℕ (left-id-on _+ℕ_ b)) >
        a +ℕ (0 +ℕ b)       ∎)

instance
    +ℤ-IsCommutative : IsCommutative _+_
    +ℤ-IsCommutative = record {commute = +-commute}

    +ℤ-IsAssociative : IsAssociative _+_
    +ℤ-IsAssociative = record { associate = +-assoc }

    +ℤ-IsBiCongruent : IsBiCongruent _+_
    +ℤ-IsBiCongruent = record { cong2 = biCongruent _+_ +-cong1 +-cong2 }

    +ℤ-Magma : Magma _+_
    +ℤ-Magma = record {}

    +ℤ-CommutativeMagma : CommutativeMagma _+_
    +ℤ-CommutativeMagma = record {}

    +ℤ-Semigroup : Semigroup _+_
    +ℤ-Semigroup = record {}

    +ℤ-CommutativeSemigroup : CommutativeSemigroup _+_ 
    +ℤ-CommutativeSemigroup = record {}

    +ℤ-HasIdentity : HasIdentity _+_ 0ℤ
    +ℤ-HasIdentity = has-identity-commute +-leftId

    +ℤ-Monoid : Monoid _+_ 0ℤ
    +ℤ-Monoid = record {}

    +ℤ-CommutativeMonoid : CommutativeMonoid _+_ 0ℤ
    +ℤ-CommutativeMonoid = record {}

private
    +-left-inv : LeftInverse _+_ 0ℤ -_
    +-left-inv (ℤ< a , b >) = zeq (begin≈
            (b +ℕ a) +ℕ 0   ≈< commute-on _+ℕ_ (b +ℕ a) 0 >
            0 +ℕ (b +ℕ a)   ≈< ≡-congruent (0 +ℕ_) _≡_ (commute-on _+ℕ_ b a) >
            0 +ℕ (a +ℕ b)   ∎)

instance
    +ℤ-HasInverse : HasInverse _+_ 0ℤ -_
    +ℤ-HasInverse = has-inverse-commute +-left-inv

    +ℤ-Group : Group _+_ 0ℤ -_
    +ℤ-Group = record {}

    +ℤ-AbelianGroup : AbelianGroup _+_ 0ℤ -_
    +ℤ-AbelianGroup = record {}
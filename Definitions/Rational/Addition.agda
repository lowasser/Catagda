{-# OPTIONS --allow-unsolved-metas #-}
module Definitions.Rational.Addition where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Definitions.Int.Base renaming (_≅_ to _=Z_; neg to negZ)
open import Definitions.Int.Addition renaming (_+_ to _+Z_)
open import Definitions.Int.Multiplication renaming (_*_ to _*Z_)
open import Definitions.Nat.Base renaming (_≅_ to _=N_; _+_ to _+N_)
open import Definitions.Nat renaming (_*_ to _*N_)
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Function.Unary.Properties
open import Definitions.Relation
open import Definitions.Either
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Ring
open import Definitions.Rational
open import Definitions.Semigroup.Commutative

_+_ : BinOp ℚ 
(p /[1+ q ]) + (r /[1+ s ]) = (ℕ-to-ℤ (suc s) *Z p +Z ℕ-to-ℤ (suc q) *Z r) /[1+ q *N s +N q +N s ]

neg : ℚ → ℚ
neg (p /[1+ q ]) = negZ p /[1+ q ]

private
    smsn=smn+m+n : (m n : ℕ) → suc m *N suc n =N suc (m *N n +N m +N n)
    smsn=smn+m+n m n = begin≅
        suc m *N suc n              ≅<>
        suc n +N (m *N suc n)       ≅< left-congruent-on _+N_ (commute-on _*N_ m (suc n)) >
        suc n +N (m +N (n *N m))    ≅<>
        suc (n +N (m +N (n *N m)))  ≅< congruent-on suc (a<bc>-to-c<ba>-on _+N_ n m (n *N m)) >
        suc ((n *N m) +N (m +N n))  ≅< congruent-on suc (right-congruent-on _+N_ (commute-on _*N_ n m)) >
        suc ((m *N n) +N m +N n)    ∎

    +-left-congruent : LeftCongruent _+_
    +-left-congruent {p /[1+ q ]} {r /[1+ s ]} {t /[1+ u ]} (q= eq) = q= {! eq  !}
{-# OPTIONS --allow-unsolved-metas #-}
module Definitions.Rational where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Definitions.Int.Base renaming (_≅_ to _=Z_; neg to negZ)
open import Definitions.Int.Addition renaming (_+_ to _+Z_)
open import Definitions.Int.Multiplication renaming (_*_ to _*Z_)
open import Definitions.Nat.Base renaming (_≅_ to _=N_; _+_ to _+N_)
open import Definitions.Nat renaming (_*_ to _*N_)
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Relation
open import Definitions.Either
open import Definitions.Setoid
open import Definitions.Setoid.Equation
open import Definitions.Ring
open import Definitions.Relation.Properties
open import Definitions.Semigroup.Commutative

open Ring {{...}}

data ℚ : Set where 
    _/[1+_] : ℤ → ℕ → ℚ

infix 5 _/[1+_]

data _≅_ : Rel lzero ℚ where
    q= : {p r : ℤ} → {q s : ℕ} → ℕ-to-ℤ (suc s) *Z p =Z ℕ-to-ℤ (suc q) *Z r → (p /[1+ q ]) ≅ (r /[1+ s ])

infix 4 _≅_

_*_ : BinOp ℚ
(p /[1+ q ]) * (r /[1+ s ]) = (p *Z r) /[1+ q *N s +N q +N s ]

0ℚ 1ℚ -1ℚ : ℚ
0ℚ = (0ℤ /[1+ 0ℕ ])
1ℚ = (1ℤ /[1+ 0ℕ ])
-1ℚ = (-1ℤ /[1+ 0ℕ ])

recip : (x : ℚ) → Either (x ≅ 0ℚ) ℚ
recip (p /[1+ q ]) with canonicalize p
... | nonneg 0ℕ , eq        = left (q= (begin≅ 
        1ℤ *Z p                     ≅< left-congruent-on _*Z_ eq >
        0ℤ                          ≅< symmetric-on ℤ (right-zero-on _*Z_ 0ℤ (ℕ-to-ℤ q)) >
        ℕ-to-ℤ (suc q) *Z 0ℤ        ∎))
... | nonneg (suc n) , eq   = right (ℕ-to-ℤ (suc q) /[1+ n ])
... | negsuc n , eq         = right (negZ (ℕ-to-ℤ (suc q)) /[1+ n ])

private
    ≅-reflexive : Reflexive _≅_
    ≅-reflexive (p /[1+ q ]) = q= (reflexive-on ℤ (ℕ-to-ℤ (suc q) *Z p))

    ≅-symmetric : Symmetric _≅_
    ≅-symmetric (q= eq) = q= (symmetric-on ℤ eq)

    ≅-transitive : Transitive _≅_
    ≅-transitive {p /[1+ q ]} {r /[1+ s ]} {t /[1+ u ]} (q= ps=rq) (q= ru=ts) = q= (cancel-left-multiplication-by-nonzero-positive s (ℕ-to-ℤ (suc u) *Z p) ((ℕ-to-ℤ (suc q) *Z t)) (begin≅
        ℕ-to-ℤ (suc s) *Z (ℕ-to-ℤ (suc u) *Z p)     ≅< a<bc>-to-b<ac>-on _*Z_ (ℕ-to-ℤ (suc s)) (ℕ-to-ℤ (suc u)) p >
        ℕ-to-ℤ (suc u) *Z (ℕ-to-ℤ (suc s) *Z p)     ≅< left-congruent-on _*Z_ ps=rq >
        ℕ-to-ℤ (suc u) *Z (ℕ-to-ℤ (suc q) *Z r)     ≅< a<bc>-to-b<ac>-on _*Z_ (ℕ-to-ℤ (suc u)) (ℕ-to-ℤ (suc q)) r >
        ℕ-to-ℤ (suc q) *Z (ℕ-to-ℤ (suc u) *Z r)     ≅< left-congruent-on _*Z_ ru=ts >
        ℕ-to-ℤ (suc q) *Z (ℕ-to-ℤ (suc s) *Z t)     ≅< a<bc>-to-b<ac>-on _*Z_ (ℕ-to-ℤ (suc q)) (ℕ-to-ℤ (suc s)) t >
        ℕ-to-ℤ (suc s) *Z (ℕ-to-ℤ (suc q) *Z t)     ∎))

instance
    ≅-setoid : Setoid lzero ℚ
    ≅-setoid = make-setoid _≅_ ≅-reflexive ≅-transitive ≅-symmetric
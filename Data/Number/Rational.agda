module Data.Number.Rational where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Int.Base renaming (_≅_ to _=Z_; neg to negZ)
open import Data.Number.Int.Addition renaming (_+_ to _+Z_)
open import Data.Number.Int.Multiplication renaming (_*_ to _*Z_)
open import Data.Number.Nat.Base renaming (_≅_ to _=N_; _+_ to _+N_)
open import Data.Number.Nat renaming (_*_ to _*N_)
open import Function.Binary
open import Function.Binary.Properties
open import Relation
open import Data.Either
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Structure.Algebraic.Ring
open import Relation.Properties
open import Structure.Algebraic.Semigroup.Commutative
open import Logic
open import Structure.Algebraic.IntegralDomain

open Ring {{...}}

private
    _≠Z_ : (a b : ℤ) → Set
    a ≠Z b = ¬ (a =Z b)

data ℚ : Set where 
    frac : (x y : ℤ) → ¬ (y =Z 0ℤ) → ℚ

data _≅_ : Rel lzero ℚ where
    q= : {p q r s : ℤ} → {q≠0 : ¬ (q =Z 0ℤ)} → {s≠0 : ¬ (s =Z 0ℤ)} → p *Z s =Z r *Z q → frac p q q≠0 ≅ frac r s s≠0

infix 4 _≅_

private
    1≠0 : ¬ (1ℤ =Z 0ℤ)
    1≠0 (z= ())

0ℚ : ℚ
0ℚ = frac 0ℤ 1ℤ 1≠0
1ℚ = frac 1ℤ 1ℤ 1≠0
-1ℚ = frac -1ℤ 1ℤ 1≠0

private
    ≅-reflexive : Reflexive _≅_
    ≅-reflexive (frac p q q≠0) = q= (reflexive-on ℤ (p *Z q))

    ≅-symmetric : Symmetric _≅_
    ≅-symmetric {frac p q q≠0} {frac r s s≠0} (q= eq) = q= (symmetric-on ℤ eq)
    
    ≅-transitive : Transitive _≅_
    ≅-transitive {frac p q q≠0} {frac r s s≠0} {frac t u u≠0} (q= ps=rq) (q= ru=ts) = q= (cancel-left-multiplication-by-nonzero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ s (p *Z u) (t *Z q) s≠0 (begin≅
        s *Z (p *Z u)       ≅< a<bc>-to-c<ba>-on _*Z_ s p u >
        u *Z (p *Z s)       ≅< left-congruent-on _*Z_ ps=rq >
        u *Z (r *Z q)       ≅< a<bc>-to-c<ba>-on _*Z_ u r q >
        q *Z (r *Z u)       ≅< left-congruent-on _*Z_ ru=ts >
        q *Z (t *Z s)       ≅< a<bc>-to-c<ba>-on _*Z_ q t s >
        s *Z (t *Z q)       ∎))

instance
    ℚ-setoid : Setoid lzero ℚ
    ℚ-setoid = make-setoid _≅_ ≅-reflexive ≅-transitive ≅-symmetric
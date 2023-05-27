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
open import Definitions.Logic
open import Definitions.IntegralDomain

open Ring {{...}}

private
    _≠Z_ : (a b : ℤ) → Set
    a ≠Z b = ¬ (a =Z b)

data ℚ : Set where 
    frac : (x y : ℤ) → ¬ (y =Z 0ℤ) → ℚ

data _≅_ : Rel lzero ℚ where
    q= : {p q r s : ℤ} → {q≠0 : ¬ (q =Z 0ℤ)} → {s≠0 : ¬ (s =Z 0ℤ)} → p *Z s =Z q *Z r → frac p q q≠0 ≅ frac r s s≠0

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
    ≅-reflexive (frac p q q≠0) = q= (commute-on _*Z_ p q)

    ≅-symmetric : Symmetric _≅_
    ≅-symmetric {frac p q q≠0} {frac r s s≠0} (q= eq) = q= (begin≅
        r *Z q      ≅< commute-on _*Z_ r q >
        q *Z r      ≅< symmetric-on ℤ eq >
        p *Z s      ≅< commute-on _*Z_ p s >
        s *Z p      ∎)
    
    ≅-transitive : Transitive _≅_
    ≅-transitive {frac p q q≠0} {frac r s s≠0} {frac t u u≠0} (q= ps=qr) (q= ru=st) = q= (cancel-left-multiplication-by-nonzero-on _*Z_ _+Z_ 1ℤ 0ℤ negZ s (p *Z u) (q *Z t) s≠0 (begin≅
        s *Z (p *Z u)       ≅< a<bc>-to-c<ba>-on _*Z_ s p u >
        u *Z (p *Z s)       ≅< left-congruent-on _*Z_ ps=qr >
        u *Z (q *Z r)       ≅< a<bc>-to-b<ca>-on _*Z_ u q r >
        q *Z (r *Z u)       ≅< left-congruent-on _*Z_ ru=st >
        q *Z (s *Z t)       ≅< a<bc>-to-b<ac>-on _*Z_ q s t >
        s *Z (q *Z t)       ∎))

instance
    ℚ-setoid : Setoid lzero ℚ
    ℚ-setoid = make-setoid _≅_ ≅-reflexive ≅-transitive ≅-symmetric
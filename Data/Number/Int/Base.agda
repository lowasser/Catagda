module Data.Number.Int.Base where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Data.Number.Nat.Base renaming (_≅_ to _=N_)
open import Data.Number.Nat.Order
open import Data.Number.Nat.Addition renaming (_+_ to _++_)
open import Relation
open import Relation.Properties
open import Structure.Setoid
open import Structure.Setoid.Equation
open import Function.Binary.Properties
open import Function.Properties
open import Function.Unary.Properties
open import Structure.Algebraic.Semigroup.Commutative
open import Logic

data ℤ : Set where 
    int : ℕ → ℕ → ℤ

0ℤ 1ℤ -1ℤ : ℤ
0ℤ = int 0ℕ 0ℕ
1ℤ = int 1ℕ 0ℕ
-1ℤ = int 0ℕ 1ℕ

pattern ℕ-to-ℤ n = int n 0ℕ

data _≅_ : Rel lzero ℤ where
    z= : { px nx py ny : ℕ } → (px ++ ny) =N (py ++ nx) → int px nx ≅ int py ny

infix 4 _≅_

-1≠0ℤ : ¬ (-1ℤ ≅ 0ℤ)
-1≠0ℤ (z= ())

private
    reflexive : Reflexive _≅_
    reflexive (int p n) = z= (reflexive-on ℕ (p ++ n))

    symmetric : Symmetric _≅_
    symmetric (z= eq) = z= (symmetric-on ℕ eq)

    transitive : Transitive _≅_
    transitive (z= {px} {nx} {py} {ny} x=y) (z= {py} {ny} {pz} {nz} y=z) = z= (left-injective-on _++_ (py ++ ny) (begin≅
        (py ++ ny) ++ (px ++ nz)        ≅< <ab><cd>-to-<ad><cb>-on _++_ py ny px nz >
        (py ++ nz) ++ (px ++ ny)        ≅< bi-congruent _++_ y=z x=y >
        (pz ++ ny) ++ (py ++ nx)        ≅< symmetric-on ℕ (<ab><cd>-to-<ad><cb>-on _++_ pz nx py ny) >
        (pz ++ nx) ++ (py ++ ny)        ≅< commute-on _++_ (pz ++ nx) (py ++ ny) >
        (py ++ ny) ++ (pz ++ nx)        ∎))
    
instance
    equivalence : Equivalence _≅_
    equivalence = make-equivalence _≅_ reflexive transitive symmetric

    setoid : Setoid lzero ℤ
    setoid = record {_≅_ = _≅_}

private
    ℕ-to-ℤ-congruent : Congruent ℕ-to-ℤ
    ℕ-to-ℤ-congruent 0ℕ= = reflexive-on ℤ 0ℤ
    ℕ-to-ℤ-congruent {x} {y} x=y = z= (begin≅
        x ++ 0ℕ         ≅< right-identity-on _++_ x >
        x               ≅< x=y >
        y               ≅< symmetric-on ℕ (right-identity-on _++_ y) >
        y ++ 0ℕ         ∎)

ℕ-Congruent→-ℤ : ℕ Congruent→ ℤ
ℕ-Congruent→-ℤ = record {cong-func = ℕ-to-ℤ; is-congruent = ℕ-to-ℤ-congruent}
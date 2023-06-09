module Data.Number.Int.Order where

open import Agda.Primitive
open import Data.Number.Nat.Base renaming (_≅_ to _=N_)
open import Data.Number.Nat.Addition renaming (_+_ to _++_)
open import Data.Number.Nat.Order hiding (≤-is-reflexive; ≤-is-transitive; ≤-is-antisymmetric; ≤-partial-order; ≤-pre-order; ≤-total-order) 
    renaming (_≤_ to _≤N_; cancel-left-+-≤ to cancel-left-+-≤N; addition-preserves-≤ to addition-preserves-≤N)
open import Relation
open import Relation.Properties
open import Relation.Order.Partial
open import Relation.Order.Total
open import Data.Number.Int.Base
open import Structure.Algebraic.Semigroup.Commutative
open import Structure.Setoid
open import Logic
open import Function.Binary.Properties

data _≤_ : Rel lzero ℤ where
    z≤ : {px py nx ny : ℕ} → px ++ ny ≤N py ++ nx → int px nx ≤ int py ny

infix 7 _≤_

private
    ≤-reflexive : Reflexive _≤_
    ≤-reflexive (int p n) = z≤ (reflexive-order-on _≤N_ (p ++ n))

    ≤-reflexive-equiv : {x y : ℤ} → x ≅ y → x ≤ y
    ≤-reflexive-equiv {int px nx} {int py ny} (z= px+ny=py+nx) = z≤ (reflexive-equiv-order-on _≤N_ px+ny=py+nx)

    ≤-transitive : Transitive _≤_
    ≤-transitive {int px nx} {int py ny} {int pz nz} (z≤ px+ny≤py+nx) (z≤ py+nz≤pz+ny) = z≤ 
        (cancel-left-+-≤N (py ++ ny) (px ++ nz) (pz ++ nx) 
            (bi-congruent-order _≤N_ (<ab><cd>-to-<cb><ad>-on _++_ py ny px nz) (<ab><cd>-to-<ad><cb>-on _++_ py ny pz nx) (addition-preserves-≤N px+ny≤py+nx py+nz≤pz+ny))) 

    ≤-antisymmetric : Antisymmetric _≤_
    ≤-antisymmetric (z≤ x≤y) (z≤ y≤x) = z= (antisymmetric-order-on _≤N_ x≤y y≤x)

    ≤-trichotomy : (x y : ℤ) → Tri _≅_ _≤_ x y
    ≤-trichotomy (int px nx) (int py ny) with trichotomy-on _≤N_ (px ++ ny) (py ++ nx)
    ... | triL is< not= not> = triL (z≤ is<) helpeq helpgt
            where   x = int px nx
                    y = int py ny
                    helpeq : ¬ (x ≅ y)
                    helpeq (z= x=y) = not= x=y
                    helpgt : ¬ (y ≤ x)
                    helpgt (z≤ y≤x) = not> y≤x
    ... | triE is= = triE (z= is=)
    ... | triG not< not= is> = triG helplt helpeq (z≤ is>)
            where   x = int px nx
                    y = int py ny
                    helpeq : ¬ (x ≅ y)
                    helpeq (z= x=y) = not= x=y
                    helplt : ¬ (x ≤ y)
                    helplt (z≤ x≤y) = not< x≤y

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

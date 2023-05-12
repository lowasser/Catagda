open import Agda.Primitive
open import Definitions.Setoid

module Definitions.Magma.Free {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} where

open import Definitions.Magma
open import Definitions.Function.Binary
open import Definitions.Function.Binary.Properties
open import Definitions.Relation
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Properties

open Setoid {{...}}

data FreeMagma : Set ℓ → Set ℓ where
    free-magma-leaf : A → FreeMagma A
    _<magma>_ : BinOp (FreeMagma A)

private    
    data _=fm=_ : Relation (FreeMagma A) where
        free-magma-leaf-= : {x y : A} → x ≈ y → free-magma-leaf x =fm= free-magma-leaf y
        free-magma-bin-= : {x y z w : FreeMagma A} → x =fm= y → z =fm= w → (x <magma> z) =fm= (y <magma> w)

    =fm-reflexive : Reflexive _=fm=_
    =fm-reflexive (free-magma-leaf x) = free-magma-leaf-= (reflexive-on A x)
    =fm-reflexive (a <magma> b) = free-magma-bin-= (=fm-reflexive a) (=fm-reflexive b)

    =fm-symmetric : Symmetric _=fm=_
    =fm-symmetric (free-magma-leaf-= x≈y) = free-magma-leaf-= (symmetric-on A x≈y)
    =fm-symmetric (free-magma-bin-= x≈y z≈w) = free-magma-bin-= (=fm-symmetric x≈y) (=fm-symmetric z≈w)

    =fm-transitive : Transitive _=fm=_
    =fm-transitive (free-magma-leaf-= x≈y) (free-magma-leaf-= y≈z) = free-magma-leaf-= (transitive-on A x≈y y≈z)
    =fm-transitive (free-magma-bin-= ax≈ay bx≈by) (free-magma-bin-= ay≈az by≈bz) =
        free-magma-bin-= (=fm-transitive ax≈ay ay≈az) (=fm-transitive bx≈by by≈bz)

instance
    =fm-IsReflexive : IsReflexive _=fm=_
    =fm-IsReflexive = record {reflexive = =fm-reflexive} 

    =fm-IsSymmetric : IsSymmetric _=fm=_ 
    =fm-IsSymmetric = record {symmetric = =fm-symmetric}

    =fm-IsTransitive : IsTransitive _=fm=_
    =fm-IsTransitive = record {transitive = =fm-transitive}

    =fm-Equivalence : Equivalence _=fm=_
    =fm-Equivalence = record {}

    free-magma-setoid : Setoid (FreeMagma A)
    free-magma-setoid = record {}

private
    magma-bicongruent : BiCongruent _<magma>_
    magma-bicongruent {a} {b} {c} {d} a≈b c≈d = free-magma-bin-= a≈b c≈d

instance
    free-magma-is-bicongruent : IsBiCongruent _<magma>_
    free-magma-is-bicongruent = record { cong2 = magma-bicongruent }

    free-magma-is-magma : Magma _<magma>_
    free-magma-is-magma = record {}
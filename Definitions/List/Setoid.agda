open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Setoid {ℓ : Level} (A : Set ℓ) {{SA : Setoid A}} where

open import Definitions.List
open import Definitions.Relation
open import Definitions.Relation.Equivalence
open import Definitions.Relation.Properties

open Setoid {{...}}

data _=[]=_ : Relation [ A ] where
    nil=[]=nil : nil =[]= nil
    cons=[]=cons : { x y : A } → x ≈ y → {xs ys : [ A ]} → xs =[]= ys → (x :: xs) =[]= (y :: ys)

private
    =[]=-reflexive : Reflexive _=[]=_
    =[]=-reflexive nil = nil=[]=nil
    =[]=-reflexive (x :: xs) = cons=[]=cons (reflexive-on A x) (=[]=-reflexive xs)

    =[]=-symmetric : Symmetric _=[]=_
    =[]=-symmetric nil=[]=nil = nil=[]=nil
    =[]=-symmetric (cons=[]=cons x≈y xs≈ys) = cons=[]=cons (symmetric-on A x≈y) (=[]=-symmetric xs≈ys)

    =[]=-transitive : Transitive _=[]=_
    =[]=-transitive nil=[]=nil nil=[]=nil = nil=[]=nil
    =[]=-transitive (cons=[]=cons x≈y xs≈ys) (cons=[]=cons y≈z ys≈zs) =
        cons=[]=cons (transitive-on A x≈y y≈z) (=[]=-transitive xs≈ys ys≈zs)

instance
    ≈[]-IsReflexive : IsReflexive _=[]=_
    ≈[]-IsReflexive = record { reflexive = =[]=-reflexive }

    ≈[]-IsSymmetric : IsSymmetric _=[]=_
    ≈[]-IsSymmetric = record { symmetric = =[]=-symmetric }

    ≈[]-IsTransitive : IsTransitive _=[]=_
    ≈[]-IsTransitive = record { transitive = =[]=-transitive }

    ≈[]-Equivalence : Equivalence _=[]=_
    ≈[]-Equivalence = record {}

    []-Setoid : Setoid [ A ]
    []-Setoid = record { _≈_ = _=[]=_ }

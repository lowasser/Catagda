open import Agda.Primitive
open import Definitions.Setoid

module Definitions.List.Setoid {ℓA ℓ=A : Level} (A : Set ℓA) {{SA : Setoid ℓ=A A}} where

open import Definitions.List
open import Definitions.Relation
open import Definitions.Relation.Properties

open Setoid {{...}}
open Equivalence {{...}}
open IsReflexive {{...}}
open IsSymmetric {{...}}
open IsTransitive {{...}}

data _=[]=_ : Rel ℓ=A [ A ] where
    []=[] : [] =[]= []
    cons=[]=cons : { x y : A } → x ≅ y → {xs ys : [ A ]} → xs =[]= ys → (x :: xs) =[]= (y :: ys)

open _=[]=_ public

private
    =[]=-reflexive : Reflexive _=[]=_
    =[]=-reflexive [] = []=[]
    =[]=-reflexive (x :: xs) = cons=[]=cons (reflexive x) (=[]=-reflexive xs)

    =[]=-symmetric : Symmetric _=[]=_
    =[]=-symmetric []=[] = []=[]
    =[]=-symmetric (cons=[]=cons x≅y xs≅ys) = cons=[]=cons (symmetric x≅y) (=[]=-symmetric xs≅ys)

    =[]=-transitive : Transitive _=[]=_
    =[]=-transitive []=[] []=[] = []=[]
    =[]=-transitive (cons=[]=cons x≅y xs≅ys) (cons=[]=cons y≅z ys≅zs) =
        cons=[]=cons (transitive x≅y y≅z) (=[]=-transitive xs≅ys ys≅zs)

instance
    []-setoid : Setoid ℓ=A [ A ]
    []-setoid = make-setoid _=[]=_ =[]=-reflexive =[]=-transitive =[]=-symmetric

open import Agda.Primitive

module Definitions.Relation.Equivalence.AllEqual {ℓ : Level} (A : Set ℓ) where

open import Definitions.Relation
open import Definitions.Relation.Properties
open import Definitions.Setoid

data _==_ : Rel ℓ A where
    eq : {x y : A} → x == y

instance
    alleq-reflexive : IsReflexive _==_
    alleq-reflexive = record {reflexive = λ _ → eq}

    alleq-symmetric : IsSymmetric _==_
    alleq-symmetric = record {symmetric = λ _ → eq}

    alleq-transitive : IsTransitive _==_
    alleq-transitive = record {transitive = λ _ _ → eq}

    alleq-preorder : PreOrder _==_
    alleq-preorder = record {}

    alleq-equivalence : Equivalence _==_
    alleq-equivalence = record {}

    alleq-setoid : Setoid ℓ A
    alleq-setoid = record {_≅_ = _==_}
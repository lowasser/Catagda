module Definitions.Top where

open import Agda.Primitive

data ⊤ : Set where
    tt : ⊤

open import Definitions.Relation.Equivalence.Structural.Properties {lzero} (⊤)
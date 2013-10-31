{-# OPTIONS --type-in-type #-}
module Monads2 where


open import Relation.Binary.HeterogeneousEquality
open import Categories

record Monad (C : Cat) : Set where
  open Cat C
  field T    : Obj → Obj
        η    : ∀ {X} → Hom X (T X)
        bind : ∀{X Y} → Hom X (T Y) → Hom (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden {T X}
        law2 : ∀{X Y}{f : Hom X (T Y)} → comp (bind f) η ≅ f
        law3 : ∀{X Y Z}{f : Hom X (T Y)}{g : Hom Y (T Z)} → 
               bind (comp (bind g) f)  ≅ comp (bind g) (bind f)

{-# OPTIONS --type-in-type #-}
module Monads2 where


open import Relation.Binary.HeterogeneousEquality
open import Categories

open Cat

record Monad (C : Cat) : Set where
  field T    : Obj C → Obj C
        η    : ∀ {X} → Hom C X (T X)
        bind : ∀{X Y} → Hom C X (T Y) → Hom C (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden C {T X}
        law2 : ∀{X Y}{f : Hom C X (T Y)} → comp C (bind f) η ≅ f
        law3 : ∀{X Y Z}{f : Hom C X (T Y)}{g : Hom C Y (T Z)} → 
               bind (comp C (bind g) f)  ≅ comp C (bind g) (bind f)

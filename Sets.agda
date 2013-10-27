{-# OPTIONS --type-in-type #-}
module Sets where

open import Utilities
open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Function

Sets : Cat
Sets = record{
  Obj  = Set;
  Hom  = λ X Y → X → Y; 
  iden = id;
  comp = λ f g → f ∘ g;
  idl  = refl; 
  idr  = refl; 
  ass  = refl}

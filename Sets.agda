{-# OPTIONS --type-in-type #-}
module Sets where

open import Utilities
open import Equality
open import Categories

Sets : Cat
Sets = record{
  Obj  = Set;
  Hom  = λ X Y → X → Y; 
  iden = id;
  comp = λ f g → f • g;
  idl  = refl; 
  idr  = refl; 
  ass  = refl}

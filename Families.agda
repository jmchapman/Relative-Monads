{-# OPTIONS --type-in-type #-}
module Families where

open import Equality
open import Categories
open import Utilities
open Cat

Fam : Set → Cat
Fam I = record {
  Obj  = I → Set;
  Hom  = λ A B → ∀ {i} → A i → B i;
  iden = id;
  comp = λ f g → f • g;
  idl  = refl;
  idr  = refl;
  ass  = refl}
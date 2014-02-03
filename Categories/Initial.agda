{-# OPTIONS --type-in-type #-}
module Categories.Initial where

open import Library
open import Categories
open import Categories.Sets
open Cat

record Init (C : Cat) : Set where
  field I : Obj C
        i : ∀{X} → Hom C I X
        law : ∀{X}{f : Hom C I X} → i {X} ≅ f 

ZeroSet : Init Sets
ZeroSet = record {I = ⊥; i = λ(); law = ext λ()}

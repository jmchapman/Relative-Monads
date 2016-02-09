module Categories.Initial where

open import Library
open import Categories
open import Categories.Sets
open Cat

record Init {a b} (C : Cat {a}{b})(I : Obj C) : Set (a ⊔ b) where
  constructor init
  field i : ∀{X} → Hom C I X
        law : ∀{X}{f : Hom C I X} → i {X} ≅ f 

ZeroSet : Init Sets ⊥
ZeroSet = record {i = λ(); law = ext λ()}

module Categories.Families where

open import Library
open import Categories

open Cat

Fam : Set → Cat
Fam I = record {
  Obj  = I → Set;
  Hom  = λ A B → ∀ {i} → A i → B i;
  iden = id;
  comp = λ f g → f ∘ g;
  idl  = refl;
  idr  = refl;
  ass  = refl}

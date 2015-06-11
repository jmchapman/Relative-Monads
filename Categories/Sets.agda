module Categories.Sets where

open import Library
open import Categories

Sets : Cat
Sets = record{
  Obj  = Set;
  Hom  = λ X Y → X → Y; 
  iden = id;
  comp = λ f g → f ∘ g;
  idl  = refl; 
  idr  = refl; 
  ass  = refl}

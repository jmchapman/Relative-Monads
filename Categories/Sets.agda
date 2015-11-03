module Categories.Sets where

open import Library
open import Categories

Sets : ∀{l} → Cat
Sets {l} = record{
  Obj  = Set l;
  Hom  = λ X Y → X → Y; 
  iden = id;
  comp = λ f g → f ∘ g;
  idl  = refl; 
  idr  = refl; 
  ass  = refl}

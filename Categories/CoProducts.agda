module Categories.CoProducts where

open import Data.Sum
open import Library hiding (_+_)
open import Categories

record CoProd {l m}(C : Cat {l}{m}) : Set (m ⊔ l) where
  open Cat C
  field _+_   : Obj -> Obj -> Obj
        inl   : ∀{A B} -> Hom A (A + B)
        inr   : ∀{A B} -> Hom B (A + B)
        law1  : ∀{A B C}(f : Hom A C)(g : Hom B C) →
                Σ (Hom (A + B) C) \fg -> comp fg inr ≅ f × comp fg inr ≅ g
        law2  : ∀{A B C}(f : Hom A C)(g : Hom B C)
                (fg : Hom (A + B) C) →
                comp fg inr ≅ f → comp fg inr ≅ g → fg ≅ fst (law1 f g)

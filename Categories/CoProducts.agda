module Categories.CoProducts where

open import Data.Sum hiding ([_,_])
open import Library hiding (_+_ ; _,_)
open import Categories

record CoProd {l m}(C : Cat {l}{m}) : Set (m ⊔ l) where
  open Cat C
  field _+_   : Obj -> Obj -> Obj
        inl   : ∀{A B} -> Hom A (A + B)
        inr   : ∀{A B} -> Hom B (A + B)
        [_,_] : ∀{A B C} -> Hom A C -> Hom B C -> Hom (A + B) C
        law1  : ∀{A B C}(f : Hom A C)(g : Hom B C) →
                comp [ f , g ] inl ≅ f
        law2  : ∀{A B C}(f : Hom A C)(g : Hom B C) →
                comp [ f , g ] inr ≅ g
        law3  : ∀{A B C}(f : Hom A C)(g : Hom B C)
                (h : Hom (A + B) C) →
                comp h inl ≅ f → comp h inr ≅ g → h ≅ [ f , g ]

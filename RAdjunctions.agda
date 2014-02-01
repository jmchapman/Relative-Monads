{-# OPTIONS --type-in-type #-}

module RAdjunctions where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors

open Cat
open Fun

record RAdj {C D : Cat}(J : Fun C D)(E : Cat) : Set where
  field L : Fun C E
        R : Fun E D
        left : {X : Obj C}{Y : Obj E} → 
               Hom E (OMap L X) Y → Hom D (OMap J X) (OMap R Y)
        right : {X : Obj C}{Y : Obj E} → 
                Hom D (OMap J X) (OMap R Y) → Hom E (OMap L X) Y
        lawa : {X : Obj C}{Y : Obj E}(f : Hom E (OMap L X) Y) → 
               right (left f) ≅ f
        lawb : {X : Obj C}{Y : Obj E}(f : Hom D (OMap J X) (OMap R Y)) →
               left (right f) ≅ f
        natleft : {X X' : Obj C}{Y Y' : Obj E}
                  (f : Hom C X' X)(g : Hom E Y Y')
                  (h : Hom E (OMap L X) Y) → 
                  comp D (HMap R g) (comp D (left h) (HMap J f)) 
                  ≅ 
                  left (comp E g (comp E h (HMap L f))) 
        natright : {X X' : Obj C}{Y Y' : Obj E}
                   (f : Hom C X' X)(g : Hom E Y Y')
                   (h : Hom D (OMap J X) (OMap R Y)) → 
                   right (comp D (HMap R g) (comp D h (HMap J f)))
                   ≅ 
                   comp E g (comp E (right h) (HMap L f)) 

module Adjunctions where

open import Library
open import Categories
open import Functors

open Cat
open Fun

record Adj {a b c d}(C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor adjunction
  field L        : Fun C D
        R        : Fun D C
        left     : {X : Obj C}{Y : Obj D} → 
                   Hom D (OMap L X) Y → Hom C X (OMap R Y)
        right    : {X : Obj C}{Y : Obj D} → 
                   Hom C X (OMap R Y) → Hom D (OMap L X) Y
        lawa     : {X : Obj C}{Y : Obj D}(f : Hom D (OMap L X) Y) → 
                   right (left f) ≅ f
        lawb     : {X : Obj C}{Y : Obj D}(f : Hom C X (OMap R Y)) →
                   left (right f) ≅ f
        natleft  : {X X' : Obj C}{Y Y' : Obj D}
                   (f : Hom C X' X)(g : Hom D Y Y')
                   (h : Hom D (OMap L X) Y) → 
                   comp C (HMap R g) (comp C (left h) f) 
                   ≅ 
                   left (comp D g (comp D h (HMap L f))) 
        natright : {X X' : Obj C}{Y Y' : Obj D}
                   (f : Hom C X' X)(g : Hom D Y Y')
                   (h : Hom C X (OMap R Y)) → 
                   right (comp C (HMap R g) (comp C h f)) 
                   ≅ 
                   comp D g (comp D (right h) (HMap L f)) 

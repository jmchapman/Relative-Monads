module RMonads.Modules where

open import Library
open import Categories
open import Functors
open import RMonads



record Mod {a}{b}{c}{d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
           (RM : RMonad J) : Set (a ⊔ c ⊔ d) where
  open Cat
  open Fun
  open RMonad RM
  field M       : Obj C → Obj D 
        mbind   : ∀ {X Y} → Hom D (OMap J X) (T Y) → Hom D (M X) (M Y)
        laweta  : ∀{X} → mbind (η {X}) ≅ iden D {M X}
        lawbind : ∀{X Y Z}
                  {f : Hom D (OMap J X) (T Y)}{g : Hom D (OMap J Y) (T Z)} → 
                  mbind (comp D (bind g) f) ≅ comp D (mbind g) (mbind f)

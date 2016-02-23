module RMonads.Modules where

open import Library
open import Categories
open import Functors
open import RMonads



record Mod {a}{b}{c}{d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
           (RM : RMonad J) : Set (a ⊔ c ⊔ d) where
  constructor mod
  open Cat
  open Fun
  open RMonad RM
  field M       : Obj C → Obj D 
        mbind   : ∀ {X Y} → Hom D (OMap J X) (T Y) → Hom D (M X) (M Y)
        laweta  : ∀{X} → mbind (η {X}) ≅ iden D {M X}
        lawbind : ∀{X Y Z}
                  {f : Hom D (OMap J X) (T Y)}{g : Hom D (OMap J Y) (T Z)} → 
                  mbind (comp D (bind g) f) ≅ comp D (mbind g) (mbind f)

-- any rel. monad is trivially a module over its J.
ModJ : forall {a}{b}{c}{d}{C : Cat {a}{b}}{D : Cat {c}{d}}
       {J : Fun C D} (RM : RMonad J) -> Mod (trivRM J)
ModJ {D = D}{J = J} RM = 
  mod T 
      (\ f -> bind (comp η f)) 
      (trans (cong bind idr) law1) 
      (trans (cong bind (trans (trans (sym ass) 
                                      (cong (\ g -> comp g _) (sym law2))) 
                               ass)) 
             law3)
  where open Fun J; open RMonad RM; open Cat D

-- any rel. monad is trivially a module over itself, 'tautalogical module'
ModRM : forall {a}{b}{c}{d}{C : Cat {a}{b}}{D : Cat {c}{d}}
       {J : Fun C D} (RM : RMonad J) -> Mod RM
ModRM RM = mod T bind law1 law3 where open RMonad RM

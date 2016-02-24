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


open import Functors.FullyFaithful
open import Isomorphism
-- if J is fully faithful then any suitably typed functor is a module for trivial rel monad given by J
ModF : forall {a}{b}{c}{d}{C : Cat {a}{b}}{D : Cat {c}{d}}
       {J : Fun C D} → Full J → Faithful J → (F : Fun C D) -> Mod (trivRM J)
ModF {C = C}{D = D}{J = J} P Q F = mod 
  (OMap F) 
  (λ f → HMap F (fst (P f)))
  (trans (cong (HMap F) (Q (trans (snd (P (Cat.iden D))) (sym $ fid J)))) (fid F))
  (trans (cong (HMap F) 
               (Q (trans (snd (P _)) 
                         (trans (cong₂ (Cat.comp D) 
                                       (sym $ snd (P _)) 
                                       (sym $ snd (P _))) 
                                (sym $ fcomp J))))) 
         (fcomp F)) where open Fun


-- any rel. monad is trivially a module over itself, 'tautalogical module'
ModRM : forall {a}{b}{c}{d}{C : Cat {a}{b}}{D : Cat {c}{d}}
       {J : Fun C D} (RM : RMonad J) -> Mod RM
ModRM RM = mod T bind law1 law3 where open RMonad RM

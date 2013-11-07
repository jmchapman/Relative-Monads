{-# OPTIONS --type-in-type #-}
module RMonads2 where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors

open Fun

record RMonad {C D : Cat}(J : Fun C D) : Set where
  open Cat
  field T    : Obj C → Obj D
        η    : ∀{X} → Hom D (OMap J  X) (T X)
        bind : ∀{X Y} → Hom D (OMap J X) (T Y) → Hom D (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden D {T X}
        law2 : ∀{X Y}{f : Hom D (OMap J X) (T Y)} → comp D (bind f) η ≅ f
        law3 : ∀{X Y Z}
               {f : Hom D (OMap J X) (T Y)}{g : Hom D (OMap J Y) (T Z)} →
               bind (comp D (bind g) f) ≅ comp D (bind g) (bind f)

open import Functors

TFun : ∀{C D}{J : Fun C D} → RMonad J → Fun C D
TFun {C}{D}{J} M = record { 
  OMap  = T; 
  HMap  = λ f → bind(comp η (HMap J f)); 
  fid   = trans (cong bind (trans (cong (comp η) (fid J)) idr)) law1;
  fcomp = λ{X}{Y}{Z}{f}{g} → trans (cong bind 
                                         (trans (trans (trans (cong (comp η) 
                                                                    (fcomp J)) 
                                                              (sym ass)) 
                                                       (cong (λ f → comp f (HMap J g)) 
                                                             (sym law2)))  
                                                ass)) 
                                  law3}
  where open RMonad M; open Cat D

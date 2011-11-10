{-# OPTIONS --type-in-type #-}
module RKleisli2 where

open import Equality
open import Categories
open import Functors
open import RMonads2

open Cat
open RMonad
open Fun

Kl : ∀{C D}{J : Fun C D}  → RMonad J → Cat
Kl {C}{D}{J} M = record{
  Obj  = Obj C; 
  Hom  = λ X Y → Hom D (OMap J X) (T M Y);
  iden = η M;
  comp = λ f g → comp D (bind M f) g;
  idl  = λ{X}{Y}{f} → trans (resp (λ g → comp D g f) (law1 M)) (idl D);
  idr  = law2 M;
  ass  =  λ{W}{X}{Y}{Z}{f}{g}{h} → 
    trans (resp (λ (f : Hom D (T M X) (T M Z)) → comp D f h) 
                (law3 M)) 
          (ass D)}
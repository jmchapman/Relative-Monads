{-# OPTIONS --type-in-type #-}
module REMAdj2 where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import Functors
open import RMonads2
open import RAdjunctions2
open import REM2
open import REMFunctors2

open Cat
open Fun
open RMonad
open RAdj
open RAlg
open RAlgMorph

REMAdj : ∀{C D}{J : Fun C D}(M : RMonad J) → RAdj J (EM M)
REMAdj {C}{D}{J} M = record {
  L = REML M;
  R = REMR M;
  left    = λ f → comp D (amor f) (η M);
  right   = λ{X}{B} f → record{
    amor = astr B f;
    ahom = sym (alaw2 B)};
  lawa    = λ f → 
    RAlgMorphEq (trans (sym (ahom f)) 
                       (trans (cong (comp D (amor f)) (law1 M)) (idr D)));
  lawb    = λ {X}{B} f → sym (alaw1 B);
  natleft = λ f g h → 
    trans (cong (comp D (amor g)) 
                (trans (ass D) 
                       (trans (cong (comp D (amor h)) (sym (law2 M)))
                              (sym (ass D))))) 
          (sym (ass D));
  natright = λ{W}{X}{Y}{Z} f g h → 
    RAlgMorphEq 
      (trans (sym (ahom g)) 
             (cong (comp D (amor g))
                   (trans (cong (astr Y) 
                                (trans (cong (λ h → comp D h (HMap J f)) 
                                             (alaw1 Y))
                                       (ass D)))
                          (alaw2 Y))))}

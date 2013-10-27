{-# OPTIONS --type-in-type #-}
module RKleisliAdj2 where

open import Utilities
open import Function
open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Naturals
open import RMonads2
open import RKleisli2
open import RAdjunctions2
open import RKleisliFunctors2
open Cat
open Fun
open NatT
open RMonad

KlAdj : ∀{C D}{J : Fun C D}(M : RMonad J) → RAdj J (Kl M)
KlAdj {C}{D}{J} M = record{
  L = RKlL M;
  R = RKlR M;
  left     = id;
  right    = id;
  lawa     = λ _ → refl;
  lawb     = λ _ → refl;
  natleft  = λ f g h → cong (comp D (bind M g)) 
                       (trans (cong (λ h → comp D h (HMap J f)) 
                                    (sym (law2 M))) 
                              (ass D));
  natright = λ f g h → cong (comp D (bind M g))
                            (trans (cong (λ h → comp D h (HMap J f)) 
                                         (sym (law2 M))) 
                                   (ass D))}

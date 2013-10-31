{-# OPTIONS --type-in-type #-}
module RKleisliFunctors2 where

open import Relation.Binary.HeterogeneousEquality
open import Function
open import Categories
open import Functors
open import Naturals
open import RMonads2
open import RKleisli2
open import RAdjunctions2

open Cat
open Fun
open NatT
open RMonad

RKlL : ∀{C D}{J : Fun C D}(M : RMonad J) → Fun C (Kl M)
RKlL {C}{D}{J} M = record{
  OMap  = id;
  HMap  = λ f → comp D (η M) (HMap J f);
  fid   = trans (cong (comp D (η M)) (fid J)) (idr D);
  fcomp = λ{X}{Y}{Z}{f}{g} → 
    trans (trans (trans (cong (comp D (η M)) (fcomp J))
                        (sym (ass D)))
                 (sym (cong (λ (f : Hom D _ _) → (comp D f (HMap J g)))
                            (law2 M))))
          (ass D)}

RKlR : ∀{C D}{J : Fun C D}(M : RMonad J) → Fun (Kl M) D
RKlR M = record{
  OMap  = T M;
  HMap  = bind M;
  fid   = law1 M;
  fcomp = law3 M}

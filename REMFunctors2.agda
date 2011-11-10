{-# OPTIONS --type-in-type #-}
module REMFunctors2 where

open import Equality
open import Categories
open import Functors
open import RMonads2
open import REM2

open Cat
open Fun
open RMonad
open RAlg
open RAlgMorph


REML : ∀{C D}{J : Fun C D}(M : RMonad J) → Fun C (EM M)
REML {C}{D}{J} M = record {
  OMap  = λ X → record {
    acar  = T M X; 
    astr  = bind M;
    alaw1 = sym (law2 M);
    alaw2 = law3 M};    
  HMap  = λ f → record {
    amor = bind M (comp D (η M) (HMap J f)); 
    ahom = sym (law3 M)};
  fid   = RAlgMorphEq (trans (resp (bind M) 
                                   (trans (resp (comp D (η M)) (fid J)) 
                                          (idr D))) 
                                   (law1 M));
  fcomp = λ{X}{Y}{Z}{f}{g} → 
    RAlgMorphEq (trans (resp (bind M)
                             (trans (trans (trans (resp (comp D (η M))
                                                        (fcomp J))
                                                  (sym (ass D)))
                                           (resp (λ f → comp D f (HMap J g)) 
                                                 (sym (law2 M))))
                                    (ass D)))
                       (law3 M))} 

REMR : ∀{C D}{J : Fun C D}(M : RMonad J) → Fun (EM M) D
REMR M = record {
  OMap  = acar; 
  HMap  = amor;
  fid   = refl; 
  fcomp = refl}

{-# OPTIONS --type-in-type #-}
module EMFunctors2 where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Monads2
open import EM2

open Cat
open Fun
open Monad
open Alg
open AlgMorph

EML : ∀{C}(M : Monad C) → Fun C (EM M)
EML {C} M = record {
  OMap = λ X → record {
    acar  = T M X; 
    astr  = λ Z → bind M; 
    alaw1 = sym (law2 M); 
    alaw2 = law3 M};
  HMap = λ f → record {
    amor = bind M (comp C (η M) f);
    ahom = sym (law3 M)};
  fid = AlgMorphEq (trans (cong (bind M) (idr C)) (law1 M));
  fcomp = λ {X}{Y}{Z}{f}{g} → 
    AlgMorphEq 
      (trans (cong (bind M) 
                   (trans (sym (ass C))  
                          (trans (cong (λ (f : Hom C _ _) → comp C f g)
                                       (sym (law2 M)))
                                 (ass C))))
             (law3 M))}

EMR : ∀{C}(M : Monad C) → Fun (EM M) C
EMR {C} M = record {
  OMap  = acar; 
  HMap  = amor;
  fid   = refl; 
  fcomp = refl}

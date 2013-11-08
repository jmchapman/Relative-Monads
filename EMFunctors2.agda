{-# OPTIONS --type-in-type #-}
open import Monads2

module EMFunctors2 {C}(M : Monad C) where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import EM2 M

open Cat C
open Fun
open Monad M
open Alg
open AlgMorph

EML : Fun C EM
EML = record {
  OMap = λ X → record {
    acar  = T X; 
    astr  = λ Z → bind; 
    alaw1 = sym law2; 
    alaw2 = law3};
  HMap = λ f → record {
    amor = bind (comp η f);
    ahom = sym law3};
  fid = AlgMorphEq (trans (cong bind idr) law1);
  fcomp = λ {X}{Y}{Z}{f}{g} → 
    AlgMorphEq 
      (trans (cong bind
                   (trans (sym ass)  
                          (trans (cong (λ (f : Hom _ _) → comp f g)
                                       (sym law2))
                                 ass)))
             law3)}

EMR : Fun EM C
EMR  = record {
  OMap  = acar; 
  HMap  = amor;
  fid   = refl; 
  fcomp = refl}

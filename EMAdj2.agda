{-# OPTIONS --type-in-type #-}
module EMAdj2 where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Monads2
open import Adjunctions2
open import EM2
open import EMFunctors2

open Cat
open Fun
open Monad
open Adj
open Alg
open AlgMorph


EMAdj : ∀{C}(M : Monad C) → Adj C (EM M)
EMAdj {C} M = record {
  L = EML M;
  R = EMR M;
  left = λ f → comp C (amor f) (η M);
  right = λ {X}{Y} f → record{amor = astr Y X f;ahom = sym (alaw2 Y)};
  lawa = λ {X}{Y}(f : AlgMorph _ Y) → 
    AlgMorphEq (trans (sym (ahom f)) 
                      (trans (cong (comp C (amor f)) (law1 M)) (idr C)));
  lawb = λ {X}{Y} f → sym (alaw1 Y);
  natleft = λ{X}{X'}{Y}{Y'} f g h → 
    trans (cong (comp C (amor g)) 
                (trans (ass C) (trans (cong (comp C (amor h)) (sym (law2 M))) 
                                            (sym (ass C))))) 
          (sym (ass C));
  natright = λ{X}{X'}{Y}{Y'} f g h → 
    AlgMorphEq (trans (sym (ahom g)) 
                      (cong (comp C (amor g)) 
                            (trans (cong (astr Y X') 
                                         (trans (cong (λ (g : Hom C _ _) → 
                                                         comp C g f) 
                                                      (alaw1 Y)) 
                                                (ass C))) 
                                   (alaw2 Y))))}

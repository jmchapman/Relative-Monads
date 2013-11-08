{-# OPTIONS --type-in-type #-}
open import Monads2
module EMAdj2 {C}(M : Monad C) where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Adjunctions2
open import EM2 M
open import EMFunctors2 M

open Cat C
open Fun
open Monad M
open Adj
open Alg
open AlgMorph


EMAdj : Adj C EM
EMAdj  = record {
  L = EML;
  R = EMR;
  left = λ f → comp (amor f) η;
  right = λ {X}{Y} f → record{amor = astr Y X f;ahom = sym (alaw2 Y)};
  lawa = λ {X}{Y}(f : AlgMorph _ Y) → 
    AlgMorphEq (trans (sym (ahom f)) 
                      (trans (cong (comp (amor f)) law1) idr));
  lawb = λ {X}{Y} f → sym (alaw1 Y);
  natleft = λ{X}{X'}{Y}{Y'} f g h → 
    trans (cong (comp (amor g)) 
                (trans ass (trans (cong (comp (amor h)) (sym law2)) 
                                            (sym ass)))) 
          (sym ass);
  natright = λ{X}{X'}{Y}{Y'} f g h → 
    AlgMorphEq (trans (sym (ahom g)) 
                      (cong (comp (amor g)) 
                            (trans (cong (astr Y X') 
                                         (trans (cong (λ (g : Hom _ _) → 
                                                         comp g f) 
                                                      (alaw1 Y)) 
                                                ass)) 
                                   (alaw2 Y))))}

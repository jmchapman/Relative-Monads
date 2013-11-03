{-# OPTIONS --type-in-type #-}
module Restriction where

open import Equality
open import Function
open import Categories
open import Functors
open import Naturals
open import Monads2
open import RMonads2

open Cat
open Fun

restrictM : {C D : Cat}(J : Fun C D) → Monad D → RMonad J
restrictM J M = let open Monad M in record {
  T    = T ∘ OMap J;
  η    = η;
  bind = bind;
  law1 = law1;
  law2 = law2; 
  law3 = law3}

open import MonadMorphs2
open import RMonadMorphs2

restrictMM : {C D : Cat}{M M' : Monad D}(J : Fun C D) → MonadMorph M M' → 
             RMonadMorph (restrictM J M) (restrictM J M')
restrictMM J MM = let open MonadMorph MM in record { 
  morph   = λ{X} → morph {OMap J X}; 
  lawη    = lawη; 
  lawbind = lawbind}

open import Adjunctions2
open import RAdjunctions2

restrictA : {C D E : Cat}(J : Fun C D) → Adj D E → RAdj J E 
restrictA J A = let open Adj A in record{
  L        = L ○ J;
  R        = R;
  left     = left;
  right    = right;
  lawa     = lawa;
  lawb     = lawb;
  natleft  = natleft ∘ HMap J;
  natright = natright ∘ HMap J}

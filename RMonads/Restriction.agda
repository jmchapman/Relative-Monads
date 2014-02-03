{-# OPTIONS --type-in-type #-}
module RMonads.Restriction where

open import Library
open import Categories
open import Functors
open import Naturals
open import Monads
open import RMonads

open Cat
open Fun

restrictM : {C D : Cat}(J : Fun C D) → Monad D → RMonad J
restrictM J M = record {
  T    = T ∘ OMap J;
  η    = η;
  bind = bind;
  law1 = law1;
  law2 = law2; 
  law3 = law3}
  where open Monad M

open import Monads.MonadMorphs
open import RMonads.RMonadMorphs

restrictMM : {C D : Cat}{M M' : Monad D}(J : Fun C D) → MonadMorph M M' → 
             RMonadMorph (restrictM J M) (restrictM J M')
restrictMM J MM = record { 
  morph   = λ{X} → morph {OMap J X}; 
  lawη    = lawη; 
  lawbind = lawbind}
  where open MonadMorph MM
open import Adjunctions
open import RAdjunctions

restrictA : {C D E : Cat}(J : Fun C D) → Adj D E → RAdj J E 
restrictA J A = record{
  L        = L ○ J;
  R        = R;
  left     = left;
  right    = right;
  lawa     = lawa;
  lawb     = lawb;
  natleft  = natleft ∘ HMap J;
  natright = natright ∘ HMap J}
  where open Adj A

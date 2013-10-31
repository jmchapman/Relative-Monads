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

open Monad

restrictM : {C D : Cat}(J : Fun C D) → Monad D → RMonad J
restrictM J M = record {
  T    = T M ∘ OMap J;
  η    = η M;
  _* = bind M;
  law1 = law1 M;
  law2 = law2 M; 
  law3 = law3 M}

open import MonadMorphs2
open import RMonadMorphs2

open MonadMorph

restrictMM : {C D : Cat}{M M' : Monad D}(J : Fun C D) → MonadMorph M M' → RMonadMorph (restrictM J M) (restrictM J M')
restrictMM J MM = record { 
  morph   = λ{X} → morph MM {OMap J X}; 
  lawη    = lawη MM; 
  lawbind = lawbind MM}

open import Adjunctions2
open import RAdjunctions2

open Adj

restrictA : {C D E : Cat}(J : Fun C D) → Adj D E → RAdj J E 
restrictA J A = record{
  L        = L A ○ J;
  R        = R A;
  left     = left A;
  right    = right A;
  lawa     = lawa A;
  lawb     = lawb A;
  natleft  = natleft A ∘ HMap J;
  natright = natright A ∘ HMap J}

{-# OPTIONS --type-in-type #-}
module Monads.CatofAdj.TermAdj where

open import Monads
open import Functors
open import Categories
open import Monads.CatofAdj
open import Categories.Terminal
open import Monads.CatofAdj.TermAdjObj
open import Monads.CatofAdj.TermAdjHom
open import Monads.CatofAdj.TermAdjUniq

EMIsTerm : {C : Cat}(M : Monad C) → Term (CatofAdj M)
EMIsTerm {C} M = record { 
  T = EMObj M;
  t = EMHom M;
  law = λ {A} {V} → HomAdjEq M
    _ 
    _ 
    (FunctorEq _ 
               _ 
               (omaplem M A V)
               (hmaplem M A V))}

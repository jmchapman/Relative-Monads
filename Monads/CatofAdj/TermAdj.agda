{-# OPTIONS --type-in-type #-}
open import Monads

module Monads.CatofAdj.TermAdj {C}(M : Monad C) where

open import Functors
open import Categories
open import Monads.CatofAdj M
open import Categories.Terminal
open import Monads.CatofAdj.TermAdjObj M
open import Monads.CatofAdj.TermAdjHom M
open import Monads.CatofAdj.TermAdjUniq M

EMIsTerm : Term CatofAdj
EMIsTerm = record { 
  T = EMObj;
  t = λ{A} → EMHom A;
  law = λ{A}{V} → HomAdjEq _ _ (FunctorEq _ _ (omaplem A V) (hmaplem A V))}

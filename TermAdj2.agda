{-# OPTIONS --type-in-type #-}
module TermAdj2 where

open import Monads2
open import Functors
open import Naturals
open import Adjunctions2
open import Equality
open import Categories
open import CatofAdj2
open import Terminal
open import EM2
open import EMAdj2
open import Adj2Mon2
open import TermAdj2Obj
open import TermAdj2Hom
open import TermAdj2Uniq

open Cat
open Fun
open Monad
open NatT
open Adj

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

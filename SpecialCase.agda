{-# OPTIONS --type-in-type #-}
module SpecialCase where

open import Categories
open import Functors
open import Naturals
open import Monads2
open import RMonads2

leftM : {C : Cat} → Monad C → RMonad (IdF C)
leftM {C} M = record {
  T    = Monad.T M;
  η    = Monad.η M;
  bind = Monad.bind M;
  law1 = Monad.law1 M;
  law2 = Monad.law2 M;
  law3 = Monad.law3 M}

rightM : {C : Cat} → RMonad (IdF C) → Monad C
rightM {C} M = record {
  T    = RMonad.T M;
  η    = RMonad.η M;
  bind = RMonad.bind M; 
  law1 = RMonad.law1 M;
  law2 = RMonad.law2 M;
  law3 = RMonad.law3 M}

open import Equality
open import Isomorphism

isoM : ∀{C} → Iso (RMonad (IdF C)) (Monad C)
isoM = record {fun = rightM; inv = leftM; law1 = λ _ → refl; law2 = λ _ → refl}

open import Adjunctions2
open import RAdjunctions2

leftA : {C D : Cat} → Adj C D → RAdj (IdF C) D
leftA {C}{D} A = record{
  L        = Adj.L A;
  R        = Adj.R A;
  left     = Adj.left A; 
  right    = Adj.right A; 
  lawa     = Adj.lawa A; 
  lawb     = Adj.lawb A; 
  natleft  = Adj.natleft A;
  natright = Adj.natright A}

rightA : {C D : Cat} → RAdj (IdF C) D → Adj C D
rightA {C}{D} A = record{
  L        = RAdj.L A;
  R        = RAdj.R A;
  left     = RAdj.left A; 
  right    = RAdj.right A; 
  lawa     = RAdj.lawa A; 
  lawb     = RAdj.lawb A; 
  natleft  = RAdj.natleft A;
  natright = RAdj.natright A}

isoA : {C D : Cat} → Iso (RAdj (IdF C) D) (Adj C D)
isoA = record {
  fun = rightA;
  inv = leftA;
  law1 = λ _ → refl; 
  law2 = λ _ → refl}

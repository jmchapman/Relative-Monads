{-# OPTIONS --type-in-type #-}
module SpecialCase where

open import Categories
open import Functors
open import Naturals
open import Monads2
open import RMonads2


leftM : {C : Cat} → Monad C → RMonad (IdF C)
leftM {C} M = record {
  T    = T;
  η    = η;
  bind = bind;
  law1 = law1;
  law2 = law2;
  law3 = law3} where open Monad M

rightM : {C : Cat} → RMonad (IdF C) → Monad C
rightM {C} M = record {
  T    = T;
  η    = η;
  bind = bind; 
  law1 = law1;
  law2 = law2;
  law3 = law3} where open RMonad M

open import Relation.Binary.HeterogeneousEquality
open import Isomorphism

isoM : ∀{C} → Iso (RMonad (IdF C)) (Monad C)
isoM = record {fun = rightM; inv = leftM; law1 = λ _ → refl; law2 = λ _ → refl}

open import MonadMorphs2
open import RMonadMorphs2

leftMM : ∀{C : Cat}{M M' : Monad C} → MonadMorph M M' → 
         RMonadMorph (leftM M) (leftM M')
leftMM MM = record { 
  morph   = morph; 
  lawη    = lawη; 
  lawbind = lawbind} where open MonadMorph MM

rightMM : ∀{C : Cat}{M M' : RMonad (IdF C)} → RMonadMorph M M' → 
          MonadMorph (rightM M) (rightM M')
rightMM MM = record { 
  morph   = morph; 
  lawη    = lawη; 
  lawbind = lawbind} where open RMonadMorph MM

isoMM : {C : Cat}{M M' : Monad C} → 
        Iso (RMonadMorph (leftM M) (leftM M')) (MonadMorph M M')
isoMM = record { 
 fun  = rightMM; 
 inv  = leftMM; 
 law1 = λ _ → refl; 
 law2 = λ _ → refl }

open import Adjunctions2
open import RAdjunctions2

leftA : {C D : Cat} → Adj C D → RAdj (IdF C) D
leftA {C}{D} A = record{
  L        = L;
  R        = R;
  left     = left; 
  right    = right; 
  lawa     = lawa; 
  lawb     = lawb; 
  natleft  = natleft;
  natright = natright} where open Adj A

rightA : {C D : Cat} → RAdj (IdF C) D → Adj C D
rightA {C}{D} A = record{
  L        = L;
  R        = R;
  left     = left; 
  right    = right; 
  lawa     = lawa; 
  lawb     = lawb; 
  natleft  = natleft;
  natright = natright} where open RAdj A

isoA : {C D : Cat} → Iso (RAdj (IdF C) D) (Adj C D)
isoA = record {
  fun = rightA;
  inv = leftA;
  law1 = λ _ → refl; 
  law2 = λ _ → refl}

{-# OPTIONS --type-in-type #-}
module KleisliFunctors2 where

open import Function
open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Naturals
open import Monads2
open import Kleisli2
open import Adjunctions2

open Cat
open Fun
open NatT
open Monad

KlL : ∀{C}(M : Monad C) → Fun C (Kl M)
KlL {C} M = record{
  OMap  = id;
  HMap  = comp C (η M);
  fid   = idr C;
  fcomp = λ{X}{Y}{Z}{f}{g} → 
    trans (trans (sym (ass C)) 
                 (cong (λ f → comp C f g) (sym (law2 M)))) (ass C) }

KlR : ∀{C}(M : Monad C) → Fun (Kl M) C
KlR {C} M = record{
  OMap  = T M;
  HMap  = bind M;
  fid   = law1 M;
  fcomp = law3 M}

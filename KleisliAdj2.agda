{-# OPTIONS --type-in-type #-}
module KleisliAdj2 where

open import Function
open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Naturals
open import Monads2
open import Kleisli2
open import Adjunctions2
open import KleisliFunctors2
open Cat
open Fun
open NatT
open Monad

KlAdj : ∀{C}(M : Monad C) → Adj C (Kl M)
KlAdj {C} M = record{
  L        = KlL M;
  R        = KlR M;
  left     = id;
  right    = id;
  lawa     = λ _ → refl;
  lawb     = λ _ → refl;
  natleft  = λ f g h → cong (comp C (bind M g)) 
                            (trans (cong (λ g → comp C g f) (sym (law2 M))) 
                                   (ass C));
  natright = λ f g h → cong (comp C (bind M g)) 
                            (trans (cong (λ g → comp C g f) (sym (law2 M))) 
                                   (ass C))}

{-# OPTIONS --type-in-type #-}
module Kleisli2 where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Monads2

open Cat
open Monad

Kl : ∀{C} → Monad C → Cat
Kl {C} M = record{
  Obj  = Obj C;
  Hom  = λ X Y → Hom C X (T M Y);
  iden = η M;
  comp = λ f g → comp C (bind M f) g;
  idl  = λ{X}{Y}{f} → trans (cong (λ g → comp C g f) (law1 M)) (idl C);
  idr  = law2 M;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → 
    trans (cong (λ (f : Hom C (T M X) (T M Z)) → comp C f h) (law3 M)) (ass C)}

module StrongArrows where

open import Library
open import Categories
open import Functors
open import MonoidalCat
open import WeakArrows

record SArrow {l m}(J : Monoidal {l}{m}) : Set (lsuc (l ⊔ m)) where
  constructor sarrow
  open Monoidal J
  open Cat C
  open Fun
  field A : Arrow C
  open Arrow A
  field fst' : ∀{X X' Y} -> R X' X -> R (OMap ⊗ (X' , Y)) (OMap ⊗ (X , Y))
  -- laws later


module StrongRMonads where

open import Library
open import Categories
open import Functors
open import MonoidalCat
open import RMonads

record SRMonad {a b c d}{M : Monoidal {a}{b}}{M' : Monoidal {c}{d}}
       (J : MonoidalFun M M') : Set (a ⊔ b ⊔ c ⊔ d) where
  constructor srmonad
  open MonoidalFun J
  field RM : RMonad F
  open RMonad RM
  open Cat
  open Monoidal
  open Fun
  field st : ∀{X Y} -> Hom (C M') (OMap (⊗ M') (T X , OMap F Y))
                                  (T (OMap (⊗ M) (X , Y)))
  -- laws later
  

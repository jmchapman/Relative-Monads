module Monads.MonadMorphs where

open import Library
open import Functors
open import Categories
open import Monads

open Fun
open Monad

record MonadMorph {a b}{C : Cat {a}{b}}(M M' : Monad C) : Set (a ⊔ b) where
  constructor monadmorph
  open Cat C
  field morph    : ∀ {X} → Hom (T M X) (T M' X)
        lawη     : ∀ {X} → comp morph (η M {X}) ≅ η M' {X}
        lawbind : ∀ {X Y}{k : Hom X (T M Y)} → 
                  comp (morph {Y}) (bind M k) 
                  ≅ 
                  comp (bind M' (comp (morph {Y}) k)) (morph {X})


{-# OPTIONS --type-in-type #-}
module MonadMorphs2 where

open import Equality
open import Functors
open import Categories
open import Monads2

open Cat
open Fun
open Monad

record MonadMorph {C : Cat}(M M' : Monad C) : Set where

  field morph    : ∀ {X} → Hom C (T M X) (T M' X)
        lawη     : ∀ {X} → comp C morph (η M {X}) ≅ η M' {X}
        lawbind : ∀ {X Y}{k : Hom C X (T M Y)} → 
                  comp C (morph {Y}) (bind M k) 
                  ≅ 
                  comp C (bind M' (comp C (morph {Y}) k)) (morph {X})


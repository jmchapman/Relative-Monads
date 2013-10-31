{-# OPTIONS --type-in-type #-}
module MonadMorphs2 where

open import Relation.Binary.HeterogeneousEquality
open import Functors
open import Categories
open import Monads2

open Fun
open Monad

record MonadMorph {C : Cat}(M M' : Monad C) : Set where
  open Cat C
  field morph    : ∀ {X} → Hom (T M X) (T M' X)
        lawη     : ∀ {X} → comp morph (η M {X}) ≅ η M' {X}
        lawbind : ∀ {X Y}{k : Hom X (T M Y)} → 
                  comp (morph {Y}) (bind M k) 
                  ≅ 
                  comp (bind M' (comp (morph {Y}) k)) (morph {X})


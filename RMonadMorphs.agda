{-# OPTIONS --type-in-type #-}
module RMonadMorphs where

open import Relation.Binary.HeterogeneousEquality
open import Functors
open import Categories
open import RMonads

open Fun
open RMonad

record RMonadMorph {C D : Cat}{J : Fun C D}(M M' : RMonad J) : Set where
  open Cat D
  field morph    : ∀ {X} → Hom (T M X) (T M' X)
        lawη     : ∀ {X} → comp morph (η M {X}) ≅ η M' {X}
        lawbind : ∀ {X Y}{k : Hom (OMap J X) (T M Y)} → 
                  comp (morph {Y}) (bind M k) 
                  ≅ 
                  comp (bind M' (comp (morph {Y}) k)) (morph {X})


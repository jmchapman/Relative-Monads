{-# OPTIONS --type-in-type #-}
module RMonadMorphs2 where

open import Relation.Binary.HeterogeneousEquality
open import Functors
open import Categories
open import RMonads2

open Cat
open Fun
open RMonad

record RMonadMorph {C D : Cat}{J : Fun C D}(M M' : RMonad J) : Set where
  field morph    : ∀ {X} → Hom D (T M X) (T M' X)
        lawη     : ∀ {X} → comp D morph (η M {X}) ≅ η M' {X}
        lawbind : ∀ {X Y}{k : Hom D (OMap J X) (T M Y)} → 
                  comp D (morph {Y}) (bind M k) 
                  ≅ 
                  comp D (bind M' (comp D (morph {Y}) k)) (morph {X})


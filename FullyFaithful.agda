{-# OPTIONS --type-in-type #-}

module FullyFaithful where

open import Equality
open import Categories
open import Functors
open import Naturals
open import Isomorphism

open Cat
open Fun

FullyFaithful : {C D : Cat}(F : Fun C D) → Set
FullyFaithful {C}{D} F = ∀ X Y → Iso (Hom D (OMap F X) (OMap F Y)) (Hom C X Y)
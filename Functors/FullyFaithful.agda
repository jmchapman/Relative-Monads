module Functors.FullyFaithful where

open import Library
open import Categories
open import Functors
open import Naturals
open import Isomorphism

open Cat
open Fun

FullyFaithful : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                (F : Fun C D) → Set (a ⊔ b ⊔ d)
FullyFaithful {C = C}{D = D} F = 
  ∀ (X Y : Obj C) → Iso (Hom D (OMap F X) (OMap F Y)) (Hom C X Y)

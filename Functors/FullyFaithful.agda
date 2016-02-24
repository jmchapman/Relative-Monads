module Functors.FullyFaithful where

open import Library
open import Categories
open import Functors
open import Naturals hiding (Iso)
open import Isomorphism

open Cat
open Fun

FullyFaithful : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                (F : Fun C D) → Set (a ⊔ b ⊔ d)
FullyFaithful {C = C}{D = D} F = 
  ∀ (X Y : Obj C) → Iso (Hom D (OMap F X) (OMap F Y)) (Hom C X Y)

Full : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                (F : Fun C D) → Set _
Full {C = C}{D = D} F = ∀ {X Y}(h : Hom D (OMap F X) (OMap F Y)) → 
  Σ (Hom C X Y) \ f -> HMap F f ≅ h  

Faithful : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                (F : Fun C D) → Set _
Faithful {C = C}{D = D} F = ∀{X Y}{f g : Hom C X Y} → HMap F f ≅ HMap F g → f ≅ g

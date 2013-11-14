{-# OPTIONS --type-in-type #-}
open import Functors
open import RMonads

module RKleisli.Adjunction {C D}{J : Fun C D}(M : RMonad J) where

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories
open import RKleisli
open import RAdjunctions
open import RKleisli.Functors J M
open Cat
open Fun
open RMonad M

KlAdj : RAdj J (Kl M)
KlAdj = record{
  L = RKlL;
  R = RKlR;
  left     = id;
  right    = id;
  lawa     = λ _ → refl;
  lawb     = λ _ → refl;
  natleft  = lem; 
  natright = lem}
  where
   lem = λ {X}{X'}{Y}{Y'} (f : Hom C X' X) (g : Hom D (OMap J Y) (T Y')) h → 
    proof
    comp D (bind g) (comp D h (HMap J f)) 
    ≅⟨ cong (λ h₁ → comp D (bind g) (comp D h₁ (HMap J f))) (sym law2) ⟩
    comp D (bind g) (comp D (comp D (bind h) η) (HMap J f))
    ≅⟨ cong (comp D (bind g)) (ass D) ⟩
    comp D (bind g) (comp D (bind h) (comp D η (HMap J f)))
    ∎

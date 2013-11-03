{-# OPTIONS --type-in-type #-}
open import Functors
open import RMonads2

module RKleisliAdj2 {C D}{J : Fun C D}(M : RMonad J) where

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories
open import Naturals
open import RKleisli2
open import RAdjunctions2
open import RKleisliFunctors2 J M
open Cat
open Fun
open NatT
open RMonad M

KlAdj : RAdj J (Kl M)
KlAdj = record{
  L = RKlL;
  R = RKlR;
  left     = id;
  right    = id;
  lawa     = λ _ → refl;
  lawb     = λ _ → refl;
  natleft  = λ f g h → 
    proof
    comp D (bind g) (comp D h (HMap J f)) 
    ≅⟨ cong (λ h₁ → comp D (bind g) (comp D h₁ (HMap J f))) (sym law2) ⟩
    comp D (bind g) (comp D (comp D (bind h) η) (HMap J f))
    ≅⟨ cong (comp D (bind g)) (ass D) ⟩
    comp D (bind g) (comp D (bind h) (comp D η (HMap J f)))
    ∎; 
  natright = λ f g h → 
    proof
    comp D (bind g) (comp D h (HMap J f))
    ≅⟨ cong (λ h → comp D (bind g) (comp D h (HMap J f))) (sym law2) ⟩
    comp D (bind g) (comp D (comp D (bind h) η) (HMap J f))
    ≅⟨ cong (comp D (bind g)) (ass D) ⟩
    comp D (bind g) (comp D (bind h) (comp D η (HMap J f))) 
    ∎}

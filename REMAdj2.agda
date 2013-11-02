{-# OPTIONS --type-in-type #-}
module REMAdj2 where

open import Relation.Binary.HeterogeneousEquality
open  ≅-Reasoning renaming (begin_ to proof_)
open import Equality
open import Categories
open import Functors
open import RMonads2
open import RAdjunctions2
open import REM2
open import REMFunctors2
open import Function

open Fun
open RAdj
open RAlg
open RAlgMorph

REMAdj : ∀{C D}{J : Fun C D}(M : RMonad J) → RAdj J (EM M)
REMAdj {C}{D}{J} M = let open Cat D; open RMonad M in record {
  L = REML M;
  R = REMR M;
  left    = λ f → comp (amor f) η;
  right   = λ{X}{B} f → record{
    amor = astr B f;
    ahom = sym (alaw2 B)};
  lawa    = λ {X}{Y} f → 
    RAlgMorphEq (
      proof 
      astr Y (comp (amor f) η) 
      ≅⟨ sym (ahom f) ⟩ 
      comp (amor f) (bind η)
      ≅⟨ cong (comp (amor f)) law1 ⟩ 
      comp (amor f) iden
      ≅⟨ idr ⟩ 
      amor f ∎);

  lawb    = λ {X}{B} f → sym (alaw1 B);
  natleft = λ f g h → 
    proof
    comp (amor g) (comp (comp (amor h) η) (HMap J f))
    ≅⟨ cong (comp (amor g)) ass ⟩
    comp (amor g) (comp (amor h) (comp η (HMap J f)))
    ≅⟨ cong (comp (amor g) ∘ comp (amor h)) (sym law2) ⟩
    comp (amor g) (comp (amor h) (comp (bind (comp η (HMap J f))) η))
    ≅⟨ cong (comp (amor g)) (sym ass) ⟩
    comp (amor g) (comp (comp (amor h) (bind (comp η (HMap J f)))) η)
    ≅⟨ sym ass ⟩
    comp (comp (amor g) (comp (amor h) (bind (comp η (HMap J f))))) η
    ∎;
  natright = λ{W}{X}{Y}{Z} f g h → 
    RAlgMorphEq (
      proof
      astr Z (comp (amor g) (comp h (HMap J f))) 
      ≅⟨ sym (ahom g) ⟩
      comp (amor g) (astr Y (comp h (HMap J f)))
      ≅⟨ cong (λ h₁ → comp (amor g) (astr Y (comp h₁ (HMap J f)))) (alaw1 Y) ⟩
      comp (amor g) (astr Y (comp (comp (astr Y h) η) (HMap J f)))
      ≅⟨ cong (comp (amor g) ∘ astr Y) ass ⟩
      comp (amor g) (astr Y (comp (astr Y h) (comp η (HMap J f))))
      ≅⟨ cong (comp (amor g)) (alaw2 Y) ⟩
      comp (amor g) (comp (astr Y h) (bind (comp η (HMap J f)))) 
      ∎)}

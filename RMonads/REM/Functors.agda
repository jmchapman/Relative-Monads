{-# OPTIONS --type-in-type #-}

open import Functors
open import RMonads

module RMonads.REM.Functors {C}{D}(J : Fun C D)(M : RMonad J) where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Equality
open import Categories
open import RMonads.REM M

open Cat
open Fun
open RAlg
open RAlgMorph
open RMonad M

REML : Fun C EM
REML = record {
  OMap  = λ X → record {
    acar  = T X; 
    astr  = bind;
    alaw1 = sym law2;
    alaw2 = law3};    
  HMap  = λ f → record {
    amor = bind (comp D η (HMap J f)); 
    ahom = sym law3};
  fid   = RAlgMorphEq (
    proof 
    bind (comp D η (HMap J (iden C))) 
    ≅⟨ cong (bind ∘ comp D η) (fid J) ⟩
    bind (comp D η (iden D)) 
    ≅⟨ cong bind (idr D) ⟩
    bind η
    ≅⟨ law1 ⟩ 
    iden D ∎);
  fcomp = λ{X}{Y}{Z}{f}{g} → RAlgMorphEq (
    proof
    bind (comp D η (HMap J (comp C f g))) 
    ≅⟨ cong (bind ∘ comp D η) (fcomp J) ⟩
    bind (comp D η (comp D (HMap J f) (HMap J g)))
    ≅⟨ cong bind (sym (ass D)) ⟩
    bind (comp D (comp D η (HMap J f)) (HMap J g))
    ≅⟨ cong (λ f₁ → bind (comp D f₁ (HMap J g))) (sym law2) ⟩
    bind (comp D (comp D (bind (comp D η (HMap J f))) η) (HMap J g))
    ≅⟨ cong bind (ass D) ⟩
    bind (comp D (bind (comp D η (HMap J f))) (comp D η (HMap J g)))
    ≅⟨ law3 ⟩
    comp D (bind (comp D η (HMap J f))) (bind (comp D η (HMap J g)))
    ∎)}

REMR : Fun EM D
REMR = record {
  OMap  = acar; 
  HMap  = amor;
  fid   = refl; 
  fcomp = refl}

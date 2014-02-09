open import Categories
open import Functors
open import RMonads

module RMonads.RKleisli.Functors {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                                 {J : Fun C D}(M : RMonad J) where

open import Library
open import RMonads.RKleisli M
open import RAdjunctions

open Cat
open Fun
open RMonad M

RKlL : Fun C Kl
RKlL = record{
  OMap  = id;
  HMap  = λ f → comp D η (HMap J f);
  fid   = 
    proof 
    comp D η (HMap J (iden C)) 
    ≅⟨ cong (comp D η) (fid J) ⟩ 
    comp D η (iden D) 
    ≅⟨ idr D ⟩
    η ∎;
  fcomp = λ{X}{Y}{Z}{f}{g} → 
    proof
    comp D η (HMap J (comp C f g)) 
    ≅⟨ cong (comp D η) (fcomp J) ⟩
    comp D η (comp D (HMap J f) (HMap J g))
    ≅⟨ sym (ass D) ⟩
    comp D (comp D η (HMap J f)) (HMap J g)
    ≅⟨ cong (λ f → comp D f (HMap J g)) (sym law2) ⟩
    comp D (comp D (bind (comp D η (HMap J f))) η) (HMap J g)
    ≅⟨ ass D ⟩
    comp D (bind (comp D η (HMap J f))) (comp D η (HMap J g)) 
    ∎}

RKlR : Fun Kl D
RKlR = record{
  OMap  = T;
  HMap  = bind;
  fid   = law1;
  fcomp = law3}

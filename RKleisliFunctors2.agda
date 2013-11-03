{-# OPTIONS --type-in-type #-}
module RKleisliFunctors2 where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Function
open import Categories
open import Functors
open import Naturals
open import RMonads2
open import RKleisli2
open import RAdjunctions2

open Cat
open Fun
open NatT

RKlL : ∀{C D}{J : Fun C D}(M : RMonad J) → Fun C (Kl M)
RKlL {C}{D}{J} M = let open RMonad M in record{
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
    trans (trans (trans (cong (comp D η) (fcomp J))
                        (sym (ass D)))
                 (sym (cong (λ (f : Hom D _ _) → (comp D f (HMap J g)))
                            law2)))
          (ass D)}

RKlR : ∀{C D}{J : Fun C D}(M : RMonad J) → Fun (Kl M) D
RKlR M = let open RMonad M in record{
  OMap  = T;
  HMap  = bind;
  fid   = law1;
  fcomp = law3}

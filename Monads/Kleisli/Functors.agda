open import Categories
open import Monads

module Monads.Kleisli.Functors {a b}{C : Cat {a}{b}}(M : Monad C) where

open import Library
open import Functors
open import Monads.Kleisli M

open Cat C
open Fun
open Monad M

KlL : Fun C Kl
KlL = record{
  OMap  = id;
  HMap  = comp η;
  fid   = idr;
  fcomp = λ{X}{Y}{Z}{f}{g} → 
    proof
    comp η (comp f g) 
    ≅⟨ sym ass ⟩
    comp (comp η f) g 
    ≅⟨ cong (λ f → comp f g) (sym law2) ⟩
    comp (comp (bind (comp η f)) η) g
    ≅⟨ ass ⟩ 
    comp (bind (comp η f)) (comp η g)
    ∎}

KlR : Fun Kl C
KlR = record{
  OMap  = T;
  HMap  = bind;
  fid   = law1;
  fcomp = law3}

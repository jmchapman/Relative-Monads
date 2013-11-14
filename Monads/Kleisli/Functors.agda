{-# OPTIONS --type-in-type #-}

open import Categories
open import Monads

module Monads.Kleisli.Functors {C}(M : Monad C) where

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Functors
open import Monads.Kleisli

open Cat C
open Fun
open Monad M

KlL : Fun C (Kl M)
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

KlR : Fun (Kl M) C
KlR = record{
  OMap  = T;
  HMap  = bind;
  fid   = law1;
  fcomp = law3}

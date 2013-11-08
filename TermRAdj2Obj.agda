{-# OPTIONS --type-in-type #-}

module TermRAdj2Obj where

open import RMonads2
open import Functors
open import Naturals
open import RAdjunctions2
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import CatofRAdj2
open import Terminal
open import REM2
open import REMAdj2
open import RAdj2RMon2

open Cat
open Fun
open NatT
open RAdj

lemX : ∀{C D}{J : Fun C D}(M : RMonad J) → R (REMAdj M) ○ L (REMAdj M) ≅ TFun M
lemX M = FunctorEq _ _ refl (λ f → refl) 

EMObj : {C D : Cat}{J : Fun C D}(M : RMonad J) → Obj (CatofAdj M)
EMObj {C}{D}{J} M = record { 
  E       = EM M;
  adj     = REMAdj M;
  law     = lemX M;
  ηlaw    = idl D;
  bindlaw = λ{X}{Y}{f} → 
    cong bind 
         (stripsubst (Hom D (OMap J X)) 
                     f 
                     (fcong Y (cong OMap (sym (lemX M)))))} where open RMonad M

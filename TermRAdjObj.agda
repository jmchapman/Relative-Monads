{-# OPTIONS --type-in-type #-}

module TermRAdjObj where

open import RMonads
open import Functors
open import Naturals
open import RAdjunctions
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import CatofRAdj
open import Categories.Terminal
open import RMonads.REM
open import RMonads.REM.Adjunction
open import RAdj2RMon

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

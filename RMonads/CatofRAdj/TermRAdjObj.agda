{-# OPTIONS --type-in-type #-}
open import Functors
open import RMonads

module RMonads.CatofRAdj.TermRAdjObj {C D}{J : Fun C D}(M : RMonad J) where

open import Library
open import Naturals
open import RAdjunctions
open import Categories
open import RMonads.CatofRAdj M
open import Categories.Terminal
open import RMonads.REM M
open import RMonads.REM.Adjunction M
open import RAdjunctions.RAdj2RMon

open Cat
open Fun
open NatT
open RAdj
open RMonad M

lemX : R REMAdj ○ L REMAdj ≅ TFun M
lemX = FunctorEq _ _ refl (λ f → refl) 

EMObj : Obj CatofAdj
EMObj = record { 
  E       = EM;
  adj     = REMAdj;
  law     = lemX;
  ηlaw    = idl D;
  bindlaw = λ{X}{Y}{f} → 
    cong bind 
         (stripsubst (Hom D (OMap J X)) 
                     f 
                     (fcong Y (cong OMap (sym lemX))))}

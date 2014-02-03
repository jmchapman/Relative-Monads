open import Categories
open import Functors
open import RMonads

module RMonads.CatofRAdj.TermRAdjObj {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                                     {J : Fun C D}(M : RMonad J) where

open import Library
open import Naturals
open import RAdjunctions
open import RMonads.CatofRAdj
open import Categories.Terminal
open import RMonads.REM
open import RMonads.REM.Adjunction
open import RAdjunctions.RAdj2RMon

open Cat
open Fun
open NatT
open RAdj

lemX : R (REMAdj M) ○ L (REMAdj M) ≅ TFun M
lemX = FunctorEq _ _ refl (λ f → refl) 

EMObj : Obj (CatofAdj M)
EMObj  = record { 
  E       = EM M;
  adj     = REMAdj M;
  law     = lemX;
  ηlaw    = idl D;
  bindlaw = λ{X}{Y}{f} → 
    cong bind 
         (stripsubst (Hom D (OMap J X)) 
                     f 
                     (fcong Y (cong OMap (sym lemX))))} where open RMonad M

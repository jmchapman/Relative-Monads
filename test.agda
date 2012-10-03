module test where

open import Categories
open import Functors
open import FunctorCat
open import Equality
open import Naturals
open Cat

foo : (A D : Cat) → Fun A (FunctorCat D A)
foo A D = record {
   OMap  = λ X → record { 
     OMap  = λ Y → X; 
     HMap  = λ f → iden A; 
     fid   = refl; 
     fcomp = sym (idl A) }; 
   HMap  = λ f → record { cmp = λ{X} → f; nat = trans (idl A) (sym (idr A)) }; 
   fid   = NatTEq refl;
   fcomp = NatTEq refl }
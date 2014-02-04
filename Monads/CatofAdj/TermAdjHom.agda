{-# OPTIONS --type-in-type #-}
open import Monads
open import Categories
import Monads.CatofAdj

module Monads.CatofAdj.TermAdjHom {C}
                                  (M : Monad C)
                                  (A : Cat.Obj (Monads.CatofAdj.CatofAdj M)) 
                                  where

open import Library
open import Functors
open import Adjunctions
open import Monads.EM M
open Monads.CatofAdj M
open import Monads.CatofAdj.TermAdjObj M

open Cat
open Fun
open ObjAdj A
open Adj adj
open Monad M

K' : Fun D EM
K' = record { 
    OMap  = λ X → record { 
      acar  = OMap R X; 
      astr  = λ Z f → subst (λ Z → Hom C Z (OMap R X)) 
                            (fcong Z (cong OMap law)) 
                            (HMap R (right f)); 
      alaw1 = λ {Z} {f} → alaw1lem
         (TFun M) 
         L
         R
         law
         η
         right 
         left
         ηlaw
         (natleft (iden C) (right f) (iden D))
         (lawb f);
      alaw2 = λ {Z} {W} {k} {f} → alaw2lem
         (TFun M) 
         L
         R
         law
         right
         bind
         natright
         (bindlaw {_}{_}{k})}; 
    HMap  = λ {X} {Y} f → record { 
      amor = HMap R f; 
      ahom = λ {Z} {g} → ahomlem 
         (TFun M) 
         L
         R 
         law 
         right
         natright}; 
    fid   = AlgMorphEq (fid R); 
    fcomp = AlgMorphEq (fcomp R)}

Llaw' : K' ○ L ≅ Adj.L (ObjAdj.adj EMObj)
Llaw' = FunctorEq 
 _ 
 _
 (ext
  (λ X →
     AlgEq (fcong X (cong OMap law))
     (
      (λ Z →
         dext
         (λ {f} {f'} p →
            Llawlem (TFun M) L R law right
            bind bindlaw p)))))
 (λ {X} {Y} f →
    AlgMorphEq' 
    (AlgEq (fcong X (cong OMap law))
     (
      (λ Z →
         dext
         (λ {f₁} {f'} p →
            Llawlem (TFun M) L R law right
            bind bindlaw p))))
    (AlgEq (fcong Y (cong OMap law))
     (
      (λ Z →
         dext
         (λ {f₁} {f'} p →
            Llawlem (TFun M) L R law right
            bind bindlaw p))))
       (dcong (refl {x = f}) 
              (ext (λ _ → cong₂ (Hom C) (fcong X (cong OMap law))
                                        (fcong Y (cong OMap law))))
              (dicong (refl {x = Y}) 
                      (ext (λ z →
                        cong (λ F → Hom C X z → Hom C (F X) (F z)) 
                             (cong OMap law)))
                      (dicong (refl {x = X}) 
                              (ext (λ z →
                                cong (λ F → ∀ {y} → 
                                        Hom C z y → Hom C (F z) (F y))
                                     (cong OMap law)))
                              (cong HMap law)))))


Rlaw' : R ≅ Adj.R (ObjAdj.adj EMObj) ○ K'
Rlaw'  = FunctorEq _ _ refl (λ f → refl)

rightlaw' : {X : Obj C} {Y : Obj D} {f : Hom C X (OMap R Y)} →
            HMap K' (right f) 
            ≅
            Adj.right (ObjAdj.adj EMObj) 
                  {X}
                  {OMap K' Y}
                  (subst (Hom C X) (fcong Y (cong OMap Rlaw')) f)
rightlaw' {X}{Y}{f} = AlgMorphEq'
  (AlgEq (fcong X (cong OMap law))
   (
    (λ Z →
       dext
       (λ {g} {g'} p →
          Llawlem (TFun M) L R law right
          bind bindlaw p))))
  refl
  (trans
   (cong
    (λ (f₁ : Hom C X (OMap R Y)) →
       HMap R (right f₁))
    (sym
     (stripsubst (Hom C X) f
      (fcong Y
       (cong OMap
        (FunctorEq R _ refl (λ {_} {_} f₁ → refl)))))))
   (sym
    (stripsubst (λ (Z : Obj C) → Hom C Z (OMap R Y)) _
     (fcong X (cong OMap law)))))

EMHom : Hom CatofAdj A EMObj
EMHom = record { 
  K        = K'; 
  Llaw     = Llaw'; 
  Rlaw     = Rlaw'; 
  rightlaw = rightlaw'}

{-# OPTIONS --type-in-type #-}
open import Categories
open import Monads
import Monads.CatofAdj
import Monads.CatofAdj.TermAdjObj

module Monads.CatofAdj.TermAdjUniq 
  {C}
  (M : Monad C)
  (A : Cat.Obj (Monads.CatofAdj.CatofAdj M)) 
  (V : Monads.CatofAdj.HomAdj M A (Monads.CatofAdj.TermAdjObj.EMObj M))
  where

open import Library
open import Functors
open import Adjunctions
import Monads.EM
open Monads.CatofAdj M
open Monads.CatofAdj.TermAdjObj M
open import Monads.CatofAdj.TermAdjHom M
open import Categories.Terminal 
open Monads.EM M
open Fun

open ObjAdj A
open Adj adj
open HomAdj V
open Cat

omaplem : OMap (HomAdj.K (EMHom A)) ≅ OMap K
omaplem = ext
  (λ X →
     AlgEq (fcong X (cong OMap Rlaw))
     (
      (λ Y →
         dext
         (λ {f} {f'} p →
            trans
            (trans
             (trans
              (stripsubst (λ Z → Hom C Z (OMap R X))
                          (HMap R (right f)) 
                          (fcong Y (cong OMap law)))
              (cong' refl (cong
                             (λ (F : Obj D → Obj C) →
                                λ (_ : Hom D (OMap L Y) X) →
                                  Hom C (F (OMap L Y)) (F X))
                             (cong OMap Rlaw))
                 (icong' refl
                  (cong
                   (λ (F : Obj D → Obj C) →
                      λ (z : Obj D) →
                        Hom D (OMap L Y) z →
                        Hom C (F (OMap L Y)) (F z))
                   (cong OMap Rlaw))
                  (icong' refl
                   (cong
                    (λ (F : Obj D → Obj C) →
                       λ (z : Obj D) →
                         {Y₁ : Obj D} → Hom D z Y₁ → Hom C (F z) (F Y₁))
                    (cong OMap Rlaw))
                   (cong HMap Rlaw) (refl {x = OMap L Y}))
                  (refl {x = X}))
                 (refl {x = right f})))
             (cong₃ (λ A₁ B → AlgMorph.amor  {A₁} {B})
              (fcong Y (cong OMap Llaw)) refl
              (rightlaw {Y} {X} {f})))
            (cong (Alg.astr (OMap K X) Y)
             (trans
              (stripsubst (Hom C Y) f (fcong X (cong OMap Rlaw)))
              p))))))

hmaplem : {X Y : Obj D}(f : Hom D X Y) →
          HMap (HomAdj.K (EMHom A)) f ≅ HMap K f 
hmaplem {X}{Y} f = AlgMorphEq'
  (fcong X omaplem) 
  (fcong Y omaplem)
  (cong' 
    refl 
    (cong (λ (F : Obj D → Obj C) → 
             λ (_ : Hom D X Y) → Hom C (F X) (F Y))
          (cong OMap Rlaw))
    (icong' refl 
            (cong (λ (F : Obj D → Obj C) →
                     λ (z : Obj D) → Hom D X z → Hom C (F X) (F z))
            (cong OMap Rlaw))
            (icong' refl 
                    (cong
                      (λ (F : Obj D → Obj C) → λ (z : Obj D) →
                         {Y₁ : Obj D} → Hom D z Y₁ → Hom C (F z) (F Y₁))
                      (cong OMap Rlaw))
                    (cong HMap Rlaw) 
                    (refl {x = X}))
            (refl {x = Y}))
    (refl {x = f}))
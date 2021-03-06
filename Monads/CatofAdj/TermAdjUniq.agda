open import Categories
open import Monads
import Monads.CatofAdj
import Monads.CatofAdj.TermAdjObj


module Monads.CatofAdj.TermAdjUniq 
  {a b}
  {C : Cat {a}{b}}
  (M : Monad C)
  (A : Monads.CatofAdj.ObjAdj M)
  (V : Monads.CatofAdj.HomAdj M A (Monads.CatofAdj.TermAdjObj.EMObj M))
  where

open import Library
open import Functors
open import Adjunctions
open Monads.CatofAdj M
open import Monads.EM M
open Monads.CatofAdj.TermAdjObj M
open import Monads.CatofAdj.TermAdjHom M A
open import Categories.Terminal
open Fun
open Adj
open ObjAdj
open Cat

omaplem : OMap (HomAdj.K EMHom ) ≅ OMap (HomAdj.K V)
omaplem = ext
  λ X → AlgEq (fcong X (cong OMap (HomAdj.Rlaw V)))
    ((ext λ Y →
        dext
        (λ {f} {f'} p →
           trans
           (trans
            (trans
             (stripsubst 
               (λ Z → Hom C Z (OMap (R (adj A)) X))
               (HMap (R (adj A)) (right (adj A) f)) 
               (fcong Y (cong OMap (law A))))
             (cong' refl (cong
                            (λ (F : Obj (D A) → Obj C) →
                               λ (_ : Hom (D A) (OMap (L (adj A)) Y) X) →
                                 Hom C (F (OMap (L (adj A)) Y)) (F X))
                            (cong OMap (HomAdj.Rlaw V)))
                (icong' refl
                 (cong
                  (λ (F : Obj (D A) → Obj C) →
                     λ (z : Obj (D A)) →
                       Hom (D A) (OMap (L (adj A)) Y) z →
                       Hom C (F (OMap (L (adj A)) Y)) (F z))
                  (cong OMap (HomAdj.Rlaw V)))
                 (icong' refl
                  (cong
                   (λ (F : Obj (D A) → Obj C) →
                      λ (z : Obj (D A)) →
                        {Y₁ : Obj (D A)} → Hom (D A) z Y₁ → Hom C (F z) (F Y₁))
                   (cong OMap (HomAdj.Rlaw V)))
                  (cong HMap (HomAdj.Rlaw V)) (refl {x = OMap (L (adj A)) Y}))
                 (refl {x = X}))
                (refl {x = right (adj A) f})))
            (cong₃ (λ A₁ B → AlgMorph.amor  {A₁} {B})
             (fcong Y (cong OMap (HomAdj.Llaw V))) refl
             (HomAdj.rightlaw V {Y} {X} {f})))
           (cong (Alg.astr (OMap (HomAdj.K V) X) Y)
            (trans
             (stripsubst (Hom C Y) f (fcong X (cong OMap (HomAdj.Rlaw V))))
             p)))))

hmaplem : {X Y : Obj (D A)} (f : Hom (D A) X Y) →
          HMap (HomAdj.K EMHom) f ≅ HMap (HomAdj.K V) f 
hmaplem {X}{Y} f = AlgMorphEq' 
  (fcong X omaplem)
  (fcong Y omaplem)
  (cong' 
    refl 
    (cong
      (λ (F : Obj (D A) → Obj C) → λ (_ : Hom (D A) X Y) → Hom C (F X) (F Y))
      (cong OMap (HomAdj.Rlaw V)))
    (icong' 
      refl 
      (cong 
        (λ (F : Obj (D A) → Obj C) → λ (z : Obj (D A)) → 
           Hom (D A) X z → Hom C (F X) (F z))
        (cong OMap (HomAdj.Rlaw V)))
      (icong' 
        refl 
        (cong 
          (λ (F : Obj (D A) → Obj C) → λ (z : Obj (D A)) → {Y₁ : Obj (D A)} → 
             Hom (D A) z Y₁ → Hom C (F z) (F Y₁))
          (cong OMap (HomAdj.Rlaw V)))
        (cong HMap (HomAdj.Rlaw V))
        (refl {x = X}))
      (refl {x = Y}))
    (refl {x = f}))

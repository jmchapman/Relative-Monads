{-# OPTIONS --type-in-type #-}
open import Categories
open import Functors
open import RMonads
import RMonads.CatofRAdj
import RMonads.CatofRAdj.TermRAdjObj

module RMonads.CatofRAdj.TermRAdjUniq
  {C D}
  {J : Fun C D}
  (M : RMonad J) 
  {A : Cat.Obj (RMonads.CatofRAdj.CatofAdj M)} 
  {V : RMonads.CatofRAdj.HomAdj M A (RMonads.CatofRAdj.TermRAdjObj.EMObj M)}
  where
open import Library
open import RAdjunctions

open RMonads.CatofRAdj M
open import Categories.Terminal
open import RMonads.REM M
open import RMonads.REM.Adjunction M
open import RAdjunctions.RAdj2RMon
open RMonads.CatofRAdj.TermRAdjObj M 
open import RMonads.CatofRAdj.TermRAdjHom M A

open Cat
open Fun
open ObjAdj A
open RAdj adj
open HomAdj V

omaplem : OMap (HomAdj.K EMHom) ≅ OMap (HomAdj.K V)
omaplem = ext (λ X → AlgEq
  (fcong X (cong OMap Rlaw)) 
  (λ Y →
       dext
       (λ {g} {g'} p →
          trans
          (trans
           (stripsubst (λ Z → Hom D Z (OMap R X))
            (HMap R (right g))
            (fcong Y (cong OMap law)))
           (cong' refl (ext (λ g₁ → 
             cong
               (λ (F : Obj E → Obj D) →
                  Hom D (F (OMap L Y)) (F X))
               (cong OMap Rlaw)))
            (icong' refl (ext (λ Z → 
              cong
                (λ (F : Obj E → Obj D) →
                   Hom E (OMap L Y) Z →
                   Hom D (F (OMap L Y)) (F Z))
                (cong OMap Rlaw)))
             (icong' 
               refl 
               (ext (λ Z → cong
                             (λ (F : Obj E → Obj D) →
                                {Y₁ : Obj E} →
                                Hom E Z Y₁ → Hom D (F Z) (F Y₁))
                             (cong OMap Rlaw))) 
              (cong HMap Rlaw)
              (refl {x = OMap L Y}))
             (refl {x = X}))
            (refl {x = right g})))
          (trans
           (cong₃ (λ A1 A2 → RAlgMorph.amor {A1} {A2})
            (fcong Y (cong OMap Llaw)) refl
            (rightlaw {Y} {X} {g}))
           (cong (RAlg.astr (OMap (HomAdj.K V) X))
            (trans
             (stripsubst (Hom D (OMap J Y)) g
              (fcong X (cong OMap Rlaw)))
             p))))))

hmaplem : {X₁ Y : Obj E} (f₁ : Hom E X₁ Y) →
          HMap (HomAdj.K EMHom) f₁ ≅ HMap (HomAdj.K V) f₁
hmaplem {X}{Y} f = lemZ 
  (fcong X omaplem) 
  (fcong Y omaplem) 
  (cong' 
    refl 
    (ext (λ Z → cong 
       (λ (F : Obj E → Obj D) → Hom D (F X) (F Y)) 
       (cong OMap Rlaw)))
    (icong' 
      refl 
      (ext (λ Z → cong
        (λ (F : Obj E → Obj D) →
           Hom E X Z → Hom D (F X) (F Z))
        (cong OMap Rlaw))) 
      (icong' 
        refl 
        (ext (λ Z → cong
                      (λ (F : Obj E → Obj D) →
                         {Y₁ : Obj E} →
                         Hom E Z Y₁ → Hom D (F Z) (F Y₁))
                      (cong OMap Rlaw))) 
        (cong HMap Rlaw) 
        (refl {x = X}))
      (refl {x = Y}))
     (refl {x = f}))

uniq : EMHom ≅ V
uniq = HomAdjEq _ _ (FunctorEq _ _ omaplem hmaplem)

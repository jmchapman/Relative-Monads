open import Categories
open import Functors
open import RMonads

module RMonads.CatofRAdj.TermRAdj {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
                                     {J : Fun C D}(M : RMonad J) where

open import Library
open import RAdjunctions
open import RMonads.CatofRAdj M
open import Categories.Terminal
open import RMonads.REM M
open import RMonads.REM.Adjunction M
open import RAdjunctions.RAdj2RMon
open import RMonads.CatofRAdj.TermRAdjObj M
open import RMonads.CatofRAdj.TermRAdjHom M

open Cat
open Fun
open RAdj

omaplem : {X : Obj CatofAdj} {f : Hom CatofAdj X EMObj} → 
          OMap (HomAdj.K (EMHom {X})) ≅ OMap (HomAdj.K f)
omaplem {A}{f} = ext (λ X → AlgEq
  (fcong X (cong OMap (HomAdj.Rlaw f))) 
  (iext λ Y →
       dext
       (λ {g} {g'} p →
          trans
          (trans
           (stripsubst (λ Z → Hom D Z (OMap (R (ObjAdj.adj A)) X))
            (HMap (R (ObjAdj.adj A)) (right (ObjAdj.adj A) g))
            (fcong Y (cong OMap (ObjAdj.law A))))
           (cong' refl (ext (λ g₁ → 
             cong
               (λ (F : Obj (ObjAdj.E A) → Obj D) →
                  Hom D (F (OMap (L (ObjAdj.adj A)) Y)) (F X))
               (cong OMap (HomAdj.Rlaw f))))
            (icong' refl (ext (λ Z → 
              cong
                (λ (F : Obj (ObjAdj.E A) → Obj D) →
                   Hom (ObjAdj.E A) (OMap (L (ObjAdj.adj A)) Y) Z →
                   Hom D (F (OMap (L (ObjAdj.adj A)) Y)) (F Z))
                (cong OMap (HomAdj.Rlaw f))))
             (icong' 
               refl 
               (ext (λ Z → cong
                             (λ (F : Obj (ObjAdj.E A) → Obj D) →
                                {Y₁ : Obj (ObjAdj.E A)} →
                                Hom (ObjAdj.E A) Z Y₁ → Hom D (F Z) (F Y₁))
                             (cong OMap (HomAdj.Rlaw f)))) 
              (cong HMap (HomAdj.Rlaw f))
              (refl {x = OMap (L (ObjAdj.adj A)) Y}))
             (refl {x = X}))
            (refl {x = right (ObjAdj.adj A) g})))
          (trans
           (cong₃ (λ A1 A2 → RAlgMorph.amor {A1}{A2})
            (fcong Y (cong OMap (HomAdj.Llaw f))) refl
            (HomAdj.rightlaw f {Y} {X} {g}))
           (cong (RAlg.astr (OMap (HomAdj.K f) X))
            (trans
             (stripsubst (Hom D (OMap J Y)) g
              (fcong X (cong OMap (HomAdj.Rlaw f))))
             p))))))


hmaplem : {X : Obj CatofAdj} {f : Hom CatofAdj X EMObj} → 
          {X₁ Y : Obj (ObjAdj.E X)} (f₁ : Hom (ObjAdj.E X) X₁ Y) →
            HMap (HomAdj.K (EMHom {X})) f₁ ≅ HMap (HomAdj.K f) f₁
hmaplem {A}{V}{X}{Y} f = lemZ
  (fcong X (omaplem {A} {V})) 
  (fcong Y (omaplem {A} {V})) 
  (cong' 
    refl 
    (ext (λ Z → cong 
       (λ (F : Obj (ObjAdj.E A) → Obj D) → Hom D (F X) (F Y)) 
       (cong OMap (HomAdj.Rlaw V))))
    (icong' 
      refl 
      (ext (λ Z → cong
        (λ (F : Obj (ObjAdj.E A) → Obj D) →
           Hom (ObjAdj.E A) X Z → Hom D (F X) (F Z))
        (cong OMap (HomAdj.Rlaw V)))) 
      (icong' 
        refl 
        (ext (λ Z → cong
                      (λ (F : Obj (ObjAdj.E A) → Obj D) →
                         {Y₁ : Obj (ObjAdj.E A)} →
                         Hom (ObjAdj.E A) Z Y₁ → Hom D (F Z) (F Y₁))
                      (cong OMap (HomAdj.Rlaw V)))) 
        (cong HMap (HomAdj.Rlaw V)) 
        (refl {x = X}))
      (refl {x = Y}))
     (refl {x = f}))


uniq : {X : Obj CatofAdj} {f : Hom CatofAdj X EMObj} →
       EMHom {X} ≅ f
uniq {X} {f} = HomAdjEq _ _ (FunctorEq _ _ 
  (omaplem {X} {f}) 
  (iext λ _ → iext λ _ → ext (hmaplem {X}{f})))

EMIsTerm : Term CatofAdj
EMIsTerm = record { 
  T   = EMObj; 
  t   = EMHom; 
  law = uniq}

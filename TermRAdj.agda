{-# OPTIONS --type-in-type #-}

module TermRAdj where

open import RMonads
open import Functors
open import RAdjunctions
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import CatofRAdj
open import Categories.Terminal
open import RMonads.REM
open import RMonads.REM.Adjunction
open import RAdj2RMon
open import TermRAdjObj
open import TermRAdjHom

open Cat
open Fun
open RAdj



omaplem : {C D : Cat}{J : Fun C D}(M : RMonad J) →
          {X : Obj (CatofAdj M)} {f : Hom (CatofAdj M) X (EMObj M)} → 
          OMap (HomAdj.K (EMHom M {X})) ≅ OMap (HomAdj.K f)
omaplem {C}{D}{J} M {A}{f} = ext (λ X → AlgEq M
  (fcong X (cong OMap (HomAdj.Rlaw f))) 
  (λ Y →
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
           (cong₃ (λ A1 A2 → RAlgMorph.amor {C} {D} {J} {M} {A1} {A2})
            (fcong Y (cong OMap (HomAdj.Llaw f))) refl
            (HomAdj.rightlaw f {Y} {X} {g}))
           (cong (RAlg.astr (OMap (HomAdj.K f) X))
            (trans
             (stripsubst (Hom D (OMap J Y)) g
              (fcong X (cong OMap (HomAdj.Rlaw f))))
             p))))))


{-
hmaplem : ∀{C}(M : Monad C)(A : ObjAdj M)(V : HomAdj A (EMObj M)){X Y : Obj (D A)} (f : Hom (D A) X Y) →
          HMap (HomAdj.K (EMHom M {A})) f ≅ HMap (HomAdj.K V) f 
hmaplem {C} M A V {X}{Y} f = lemZ (fcong X (omaplem M A V)) 
                                  (fcong Y (omaplem M A V)) 
                                  (cong' refl (cong
                                                 (λ (F : Obj (D A) → Obj C) →
                                                    λ (_ : Hom (D A) X Y) → Hom C (F X) (F Y))
                                                 (cong OMap (HomAdj.Rlaw V)))
                                     (icong' refl (cong
                                                     (λ (F : Obj (D A) → Obj C) →
                                                        λ (z : Obj (D A)) → Hom (D A) X z → Hom C (F X) (F z))
                                                     (cong OMap (HomAdj.Rlaw V)))
                                      (icong' refl (cong
                                                      (λ (F : Obj (D A) → Obj C) →
                                                         λ (z : Obj (D A)) →
                                                           {Y₁ : Obj (D A)} → Hom (D A) z Y₁ → Hom C (F z) (F Y₁))
                                                      (cong OMap (HomAdj.Rlaw V))) (cong HMap (HomAdj.Rlaw V)) (refl {a = X}))
                                      (refl {a = Y}))
                                     (refl {a = f}))
-}



hmaplem : {C D : Cat}{J : Fun C D}(M : RMonad J) →
          {X : Obj (CatofAdj M)} {f : Hom (CatofAdj M) X (EMObj M)} → 
          {X₁ Y : Obj (ObjAdj.E X)} (f₁ : Hom (ObjAdj.E X) X₁ Y) →
            HMap (HomAdj.K (EMHom M {X})) f₁ ≅ HMap (HomAdj.K f) f₁
hmaplem {C}{D}{J} M {A}{V}{X}{Y} f = lemZ M
  (fcong X (omaplem M {A} {V})) 
  (fcong Y (omaplem M {A} {V})) 
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

uniq : {C D : Cat}{J : Fun C D}(M : RMonad J) →
       {X : Obj (CatofAdj M)} {f : Hom (CatofAdj M) X (EMObj M)} →
       EMHom M {X} ≅ f
uniq {C}{D}{J} M {X} {f} = HomAdjEq _ _ (FunctorEq _ _ 
  (omaplem M {X} {f}) 
  (hmaplem M {X} {f}))

EMIsTerm : {C D : Cat}{J : Fun C D}(M : RMonad J) → Term (CatofAdj M)
EMIsTerm {C}{D}{J} M = record { 
  T   = EMObj M; 
  t   = EMHom M; 
  law = uniq M}

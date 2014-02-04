{-# OPTIONS --type-in-type #-}
open import Monads

module Monads.CatofAdj.TermAdjObj {C}(M : Monad C) where

open import Library
open import Functors
open import Naturals
open import Adjunctions
open import Categories
open import Monads.CatofAdj M
open import Categories.Terminal
open import Monads.EM M
open import Monads.EM.Adjunction M
open import Adjunctions.Adj2Mon

open Cat
open Fun
open Monad M
open NatT
open Adj

lemX : R EMAdj ○ L EMAdj ≅ TFun M
lemX = FunctorEq _ _ refl (λ f → refl) 

EMObj : Obj CatofAdj
EMObj = record { 
  D       = EM;
  adj     = EMAdj;
  law     = lemX;
  ηlaw    = idl C;
  bindlaw = λ{X Y f} → 
    cong bind 
         (stripsubst (Hom C X) f (fcong Y (cong OMap (sym lemX))))}


open ObjAdj
open Adj

alaw1lem : ∀{D}(T : Fun C C)(L : Fun C D)(R : Fun D C)(p : R ○ L ≅ T)
  (η : ∀ {X} → Hom C X (OMap T X)) → 
  (right : ∀ {X Y} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) → 
  (left : ∀ {X Y} → Hom D (OMap L X) Y → Hom C X (OMap R Y)) → 
  (ηlaw : ∀ {X} → left (iden D {OMap L X}) ≅ η {X}) → 
  ∀ {X}{Z}{f : Hom C Z (OMap R X)} → 
  (nat : comp C (HMap R (right f)) (comp C (left (iden D)) (iden C))
         ≅
         left (comp D (right f) (comp D (iden D) (HMap L (iden C))))) →
  (lawb : left (right f) ≅ f) → 
  f 
  ≅
  comp C (subst (λ Z₁ → Hom C Z₁ (OMap R X)) 
                (fcong Z (cong OMap p))
                (HMap R (right f))) 
         η
alaw1lem {D} .(R ○ L) L R refl η right left ηlaw {X}{Z}{f} nat lawb = 
  trans (trans (trans (sym lawb) 
                      (cong left 
                            (trans (sym (idr D)) 
                                   (cong (comp D (right f)) 
                                         (trans (sym (fid L))
                                                (sym (idl D)))))))
               (trans (sym nat) 
                      (cong (comp C (HMap R (right f))) 
                            (idr C)))) 
        (cong (comp C (HMap R (right f))) ηlaw)

alaw2lem : ∀{D}(T : Fun C C)(L : Fun C D)(R : Fun D C)(p : R ○ L ≅ T) → 
  (right : ∀ {X Y} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) → 
  (bind : ∀ {X Y} → Hom C X (OMap T Y) → Hom C (OMap T X) (OMap T Y)) → 
  (natright : {X₁ X' : Obj C} {Y Y' : Obj D} (f₁ : Hom C X' X₁)
    (g : Hom D Y Y') (h : Hom C X₁ (OMap R Y)) →
    right (comp C (HMap R g) (comp C h f₁)) 
    ≅
    comp D g (comp D (right h) (HMap L f₁))) → 
  ∀ {X}{Z} {W} {k : Hom C Z (OMap T W)}{f : Hom C W (OMap R X)} → 
  (bindlaw : HMap R (right (subst (Hom C Z) (fcong W (cong OMap (sym p))) k)) 
             ≅ bind k) → 
  subst (λ Z → Hom C Z (OMap R X))
  (fcong Z (cong OMap p))
  (HMap R
   (right
    (comp C
     (subst (λ Z → Hom C Z (OMap R X))
      (fcong W (cong OMap p)) (HMap R (right f)))
     k)))
  ≅
  comp C
  (subst (λ Z → Hom C Z (OMap R X))
   (fcong W (cong OMap p)) (HMap R (right f)))
  (bind k)
alaw2lem {D} .(R ○ L) L R refl right bind natright {X}{Z}{W}{k}{f} bindlaw =
  trans (trans (cong (HMap R) 
                     (trans (cong (λ k₁ → right (comp C (HMap R (right f)) k₁))
                                  (sym (idr C))) 
                            (trans (natright (iden C) (right f) k) 
                                   (trans (cong (λ h → comp D 
                                                            (right f) 
                                                            (comp D 
                                                                  (right k) 
                                                                  h))
                                                (fid L))
                                          (trans (sym (ass D)) 
                                                 (idr D))))))
               (fcomp R)) 
        (cong (comp C (HMap R (right f))) bindlaw)


ahomlem : ∀{D}(T : Fun C C)(L : Fun C D)(R : Fun D C)(p : R ○ L ≅ T) → 
  (right : ∀ {X Y} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
  (natright : {X₁ X' : Obj C} {Y Y' : Obj D} (f₁ : Hom C X' X₁)
    (g : Hom D Y Y') (h : Hom C X₁ (OMap R Y)) →
    right (comp C (HMap R g) (comp C h f₁)) 
    ≅
    comp D g (comp D (right h) (HMap L f₁))) → 
  {X : Obj D}{Y : Obj D}{f : Hom D X Y} →
  {Z : Obj C} {f₁ : Hom C Z (OMap R X)} →
  comp C (HMap R f)
  (subst (λ Z₁ → Hom C Z₁ (OMap R X))
   (fcong Z (cong OMap p))
   (HMap R (right f₁))) 
  ≅
  subst (λ Z₁ → Hom C Z₁ (OMap R Y))
  (fcong Z (cong OMap p))
  (HMap R (right (comp C (HMap R f) f₁)))
ahomlem {D} .(R ○ L) L R refl right natright {X}{Y}{f}{Z}{g} = 
  trans (sym (fcomp R))
    (cong (HMap R)
     (sym
      (trans (cong (λ g₁ → right (comp C (HMap R f) g₁)) (sym (idr C)))
       (trans (natright (iden C) f g)
        (trans (cong (λ h → comp D f (comp D (right g) h)) (fid L))
         (trans (sym (ass D)) (idr D)))))))


Llawlem : ∀{D}(T : Fun C C)(L : Fun C D)(R : Fun D C)(p : R ○ L ≅ T) → 
  (right : ∀ {X Y} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) → 
  (bind : ∀ {X Y} → Hom C X (OMap T Y) → Hom C (OMap T X) (OMap T Y)) → 
  (bindlaw : {X Y : Obj C} {f : Hom C X (OMap T Y)} →
    HMap R
    (right
     (subst (Hom C X) (fcong Y (cong OMap (sym p))) f))
    ≅ bind f) → 
  ∀{X Z} → 
  {f  : Hom C Z (OMap R (OMap L X))}
  {f' : Hom C Z (OMap T X)} → (q  : f ≅ f') → 
  subst (λ Z₁ → Hom C Z₁ (OMap R (OMap L X)))
  (fcong Z (cong OMap p)) (HMap R (right f))
  ≅ bind f'
Llawlem .(R ○ L) L R refl right bind bindlaw {X}{Z}{f}{.f} refl = bindlaw


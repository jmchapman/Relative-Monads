{-# OPTIONS --type-in-type #-}
open import Monads

module Monads.CatofAdj {C}(M : Monad C) where

open import Library
open import Categories
open import Functors
open import Adjunctions

open Fun
open Monad
open Adj
open Cat


record ObjAdj : Set where
  field D   : Cat
        adj : Adj C D
        law : R adj ○ L adj ≅ TFun M
        ηlaw : ∀ {X} → left adj (iden D {OMap (L adj) X}) ≅ Monad.η M {X} 
        bindlaw : ∀{X Y}{f : Hom C X (T M Y)} → 
          HMap (R adj) 
               (right adj 
                      (subst (Hom C X) (fcong Y (cong OMap (sym law))) f)) 
          ≅ 
          Monad.bind M f
open ObjAdj

record HomAdj (A B : ObjAdj) : Set where
  field K : Fun (D A) (D B)
        Llaw : K ○ L (adj A) ≅ L (adj B)  
        Rlaw : R (adj A) ≅ R (adj B) ○ K
        rightlaw : {X : Obj C}{Y : Obj (D A)}
                   {f : Hom C X (OMap (R (adj A)) Y)} →  
                   HMap K (right (adj A) {X}{Y} f) 
                   ≅ 
                   right (adj B) 
                         {X}
                         {OMap K Y} 
                         (subst (Hom C X) (fcong Y (cong OMap Rlaw)) f)
open HomAdj

HomAdjEq : {A B : ObjAdj}(f g : HomAdj A B) → 
           K f ≅ K g → f ≅ g
HomAdjEq {A}{B} f g p = funnycong4
  {Fun (D A) (D B)}
  {λ K → K ○ L (adj A) ≅ L (adj B)}
  {λ K Llaw → R (adj A) ≅ R (adj B) ○ K}
  {λ K Llaw Rlaw → {X : Obj C}{Y : Obj (D A)}
                   {f : Hom C X (OMap (R (adj A)) Y)} →  
                   HMap K (right (adj A) {X}{Y} f) 
                   ≅
                   right (adj B) 
                         {X}
                         {OMap K Y} 
                         (subst (Hom C X) (fcong Y (cong OMap Rlaw)) f)}
  (λ x y z z' → record{K = x;Llaw = y;Rlaw = z; rightlaw = z'})
  p 
  (fixtypes' refl)
  (fixtypes refl)
  (iext λ X → iext λ Y → iext λ h → 
    fixtypes (cong (λ F → HMap F (right (adj A) h)) p))

rightlawlem : ∀{D}(R : Fun D C)(L : Fun C D)
  (p : OMap R ≅ OMap (R ○ (IdF D))) → 
  (right : {X : Obj C}{Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
           {Z : Obj C}{Y : Obj D}{f : Hom C Z (OMap R Y)} →
  right f ≅ right (subst (Hom C Z) (fcong Y p) f)
rightlawlem R L refl right = refl

idHomAdj : {X : ObjAdj} → HomAdj X X
idHomAdj {X} = record {
    K = IdF (D X);
    Llaw = FunctorEq _ _ refl (λ _ → refl);
    Rlaw = FunctorEq _ _ refl (λ _ → refl);
    rightlaw = rightlawlem (R (adj X)) 
                           (L (adj X)) 
                           (cong OMap (FunctorEq _ _ refl (λ _ → refl))) 
                           (right (adj X))}

HMaplem : ∀{C D}{X X' Y Y' : Obj C} → X ≅ X' → Y ≅ Y' → 
          {f : Hom C X Y}{f' : Hom C X' Y'} → f ≅ f' → (F : Fun C D) → 
          HMap F {X}{Y} f ≅ HMap F {X'}{Y'} f'
HMaplem refl refl refl F = refl


rightlawlem2 : ∀{D E F}
  (RX : Fun D C)
  (LX : Fun C D)
  (RY : Fun E C)
  (LY : Fun C E)
  (RZ : Fun F C)
  (LZ : Fun C F)
  (KA : Fun D E)
  (KB : Fun E F) → 
  (rightX : {X : Obj C}{Y : Obj D} → 
            Hom C X (OMap RX Y) → Hom D (OMap LX X) Y)
  (rightY : {X : Obj C}{Y : Obj E} → 
            Hom C X (OMap RY Y) → Hom E (OMap LY X) Y)
  (rightZ : {X : Obj C}{Y : Obj F} → 
            Hom C X (OMap RZ Y) → Hom F (OMap LZ X) Y) → 
  (p : RY ≅ RZ ○ KB)
  (q : RX ≅ RY ○ KA) →
  (p' : KA ○ LX ≅ LY) → 
  (r : {X : Obj C}{Y : Obj E}{f : Hom C X (OMap RY Y)} →
       HMap KB (rightY f) 
       ≅ 
       rightZ (subst (Hom C X) (fcong Y (cong OMap p)) f)) →
  (s : {X : Obj C}{Y : Obj D}{f : Hom C X (OMap RX Y)} →
       HMap KA (rightX f) 
       ≅ 
       rightY (subst (Hom C X) (fcong Y (cong OMap q)) f)) →
  ∀{A B}(h : Hom C A (OMap RX B)) → 
  HMap (KB ○ KA) (rightX h) ≅
  rightZ
  (subst (Hom C A) (fcong B (cong OMap (trans q (cong (λ F → F ○ KA) p)))) h)
rightlawlem2 {D}{E}{F} 
             .((RZ ○ KB) ○ KA) LX .(RZ ○ KB) .(KA ○ LX) 
             RZ LZ KA KB 
             rightX rightY rightZ 
             refl refl refl 
             r s h = 
  proof 
  HMap (KB ○ KA) (rightX h)
  ≅⟨ cong (HMap KB) s ⟩
  HMap KB (rightY h)
  ≅⟨ r ⟩ 
  rightZ h 
  ∎

compLlaw : {X Y Z : ObjAdj}(f :  HomAdj Y Z)(g : HomAdj X Y) →
           (K f ○ K g) ○ L (adj X) ≅ L (adj Z)
compLlaw {X}{Y}{Z} f g = 
  FunctorEq 
    _ 
    _
    (ext λ A → 
      proof
      OMap (K f) (OMap (K g) (OMap (L (adj X)) A))
      ≅⟨ cong (λ F → OMap (K f) (OMap F A)) (Llaw g) ⟩ 
      OMap (K f) (OMap (L (adj Y)) A)
      ≅⟨ cong (λ F → OMap F A) (Llaw f) ⟩ 
      OMap (L (adj Z)) A ∎)
    (λ {A} {B} h → 
      proof
      HMap (K f) (HMap (K g) (HMap (L (adj X)) h)) 
      ≅⟨ HMaplem (cong (λ F → OMap F A) (Llaw g))
                 (cong (λ F → OMap F B) (Llaw g))
                 (cong (λ F → HMap F h) (Llaw g))
                 (K f) ⟩
      HMap (K f) (HMap (L (adj Y)) h)
      ≅⟨ cong (λ F → HMap F h) (Llaw f) ⟩
      HMap (L (adj Z)) h 
      ∎)

compRlaw : {X Y Z : ObjAdj}(f :  HomAdj Y Z)(g : HomAdj X Y) →
           R (adj X) ≅ R (adj Z) ○ (K f ○ K g)
compRlaw {X}{Y}{Z} f g = 
  FunctorEq 
    _ 
    _
    (ext λ A → 
      trans (cong (λ F → OMap F A) (Rlaw g))
            (cong (λ F → OMap F (OMap (K g) A)) (Rlaw f)))

{-      proof
      OMap (R (adj X)) A 
      ≅⟨ cong (λ F → OMap F A) (Rlaw g) ⟩
      OMap (R (adj Y)) (OMap (K g) A)
      ≅⟨ {!cong (λ F → OMap F (OMap (K g) A)) (Rlaw f)!} ⟩
      OMap (R (adj Z)) (OMap (K f) (OMap (K g) A)) 
      ∎) -}
    (λ {A} {B} h →
      trans (cong (λ F → HMap F h) (Rlaw g))
            (cong (λ F → HMap F (HMap (K g) h)) (Rlaw f)))

comprightlaw : {X Y Z : ObjAdj} → 
               (f :  HomAdj Y Z)(g : HomAdj X Y) →
               {X₁ : Obj C}{Y₁ : Obj (D X)}
               {f₁ : Hom C X₁ (OMap (R (adj X)) Y₁)} →
               HMap (K f ○ K g) (right (adj X) f₁) 
               ≅
               right (adj Z)
                     (subst (Hom C X₁) 
                            (fcong Y₁ (cong OMap (compRlaw f g))) 
                            f₁)
comprightlaw {X}{Y}{Z} f g {A}{B}{h} = 
  trans
    (rightlawlem2 (R (adj X)) 
                  (L (adj X)) 
                  (R (adj Y))
                  (L (adj Y))
                  (R (adj Z)) 
                  (L (adj Z))
                  (K g) 
                  (K f) 
                  (right (adj X)) 
                  (right (adj Y))
                  (right (adj Z)) 
                  (Rlaw f)
                  (Rlaw g) 
                  (Llaw g)
                  (rightlaw f)
                  (rightlaw g) 
                  h)
    (cong 
      (right (adj Z))
      (trans
        (stripsubst (Hom C A) 
                    h
                    (fcong B 
                           (cong OMap 
                                 (trans (Rlaw g) 
                                        (cong (λ F₁ → F₁ ○ K g) 
                                              (Rlaw f))))))
        (sym
          (stripsubst 
            (Hom C A) 
            h
            (fcong B
                   (cong OMap
                         (FunctorEq (R (adj X)) 
                                    _
                                    (ext (λ A₁ →
                                      trans (cong (λ F → OMap F A₁) (Rlaw g))
                                            (cong (λ F → OMap F 
                                                              (OMap (K g) A₁)) 
                                                  (Rlaw f))))
                                    (λ {A₁} {B₁} h₁ → trans 
                                      (cong (λ F → HMap F h₁) (Rlaw g))
                                      (cong (λ F → HMap F (HMap (K g) h₁)) 
                                            (Rlaw f))))))))))

compHomAdj : {X Y Z : ObjAdj} → 
             HomAdj Y Z → HomAdj X Y → HomAdj X Z
compHomAdj {X}{Y}{Z} f g = record {
    K        = K f ○ K g;
    Llaw     = compLlaw f g;
    Rlaw     = compRlaw f g;
    rightlaw = comprightlaw f g}

idlHomAdj : {X Y : ObjAdj}{f : HomAdj X Y} → 
            compHomAdj idHomAdj f ≅ f
idlHomAdj{X}{Y}{f} = 
  HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))

idrHomAdj : {X : ObjAdj}{Y : ObjAdj}{f : HomAdj X Y} → 
            compHomAdj f idHomAdj ≅ f
idrHomAdj {X}{Y}{f} = 
  HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))

assHomAdj : {W X Y Z : ObjAdj}
            {f : HomAdj Y Z} {g : HomAdj X Y} {h : HomAdj W X} →
            compHomAdj (compHomAdj f g) h ≅ compHomAdj f (compHomAdj g h)
assHomAdj {W}{X}{Y}{Z}{f}{g}{h} = 
  HomAdjEq _ _ (FunctorEq _ _ refl (λ h → refl))

CatofAdj : Cat
CatofAdj = record{
  Obj  = ObjAdj;
  Hom  = HomAdj;
  iden = idHomAdj;
  comp = compHomAdj;
  idl  = idlHomAdj;
  idr  = idrHomAdj;
  ass  = λ{W X Y Z f g h} → assHomAdj {W}{X}{Y}{Z}{f}{g}{h}}

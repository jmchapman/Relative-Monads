{-# OPTIONS --type-in-type #-}
module CatofAdj2 where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import Functors
open import Monads2
open import Adjunctions2

open Fun
open Monad
open Adj
open Cat


record ObjAdj {C : Cat}(M : Monad C) : Set where
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

record HomAdj {C : Cat}{M : Monad C}(A B : ObjAdj M) : Set where
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

HomAdjEq : {C : Cat}{M : Monad C}{A B : ObjAdj M}(f g : HomAdj A B) → 
           K f ≅ K g → f ≅ g
HomAdjEq {C}{M}{A}{B} f g p = funnycong4
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
  {HomAdj A B}
  (λ x y z z' → record{K = x;Llaw = y;Rlaw = z; rightlaw = z'})
  p 
  (fixtypes (sym (Llaw g)))
  (fixtypes (sym (Rlaw f)))
  (iext (λ X → iext (λ Y → iext (λ h → 
     fixtypes (trans (sym (rightlaw f {X} {Y} {h})) 
              (cong (λ F → HMap F (right (adj A) h)) p))))))

rightlawlem : ∀{C D}(R : Fun D C)(L : Fun C D)
  (p : OMap R ≅ OMap (R ○ (IdF D))) → 
  (right : {X : Obj C}{Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
           {X₁ : Obj C}{Y : Obj D}{f : Hom C X₁ (OMap R Y)} →
  right f ≅ right (subst (Hom C X₁) (fcong Y p) f)
rightlawlem R L refl right {X}{Y}{f} = refl

idHomAdj : {C : Cat}{M : Monad C}{X : ObjAdj M} → HomAdj X X
idHomAdj {C}{M}{X} = record {
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


rightlawlem2 : ∀{C D E F}
  (RX : Fun D C)
  (LX : Fun C D)
  (RY : Fun E C)
  (LY : Fun C E)
  (RZ : Fun F C)
  (LZ : Fun C F)
  (KA : Fun D E)
  (KB : Fun E F) → 
  (rightX : {X₁ : Obj C}{Y₁ : Obj D} → 
            Hom C X₁ (OMap RX Y₁) → Hom D (OMap LX X₁) Y₁)
  (rightY : {X₁ : Obj C}{Y₁ : Obj E} → 
            Hom C X₁ (OMap RY Y₁) → Hom E (OMap LY X₁) Y₁)
  (rightZ : {X₁ : Obj C}{Y₁ : Obj F} → 
            Hom C X₁ (OMap RZ Y₁) → Hom F (OMap LZ X₁) Y₁) → 
  (p : RY ≅ RZ ○ KB)
  (q : RX ≅ RY ○ KA) →
  (p' : KA ○ LX ≅ LY) → 
  (r : {X₁ : Obj C}{Y₁ : Obj E}{f₁ : Hom C X₁ (OMap RY Y₁)} →
       HMap KB (rightY f₁) 
       ≅ 
       rightZ (subst (Hom C X₁) (fcong Y₁ (cong OMap p)) f₁)) →
  (s : {X₁ : Obj C}{Y₁ : Obj D}{f₁ : Hom C X₁ (OMap RX Y₁)} →
       HMap KA (rightX f₁) 
       ≅ 
       rightY (subst (Hom C X₁) (fcong Y₁ (cong OMap q)) f₁)) →
  ∀{A B}(h : Hom C A (OMap RX B)) → 
  HMap (KB ○ KA) (rightX h) ≅
  rightZ
  (subst (Hom C A) (fcong B (cong OMap (trans q (cong (λ F₁ → F₁ ○ KA) p)))) h)
rightlawlem2 {C}{D}{E}{F} .((RZ ○ KB) ○ KA) LX .(RZ ○ KB) .(KA ○ LX) RZ LZ KA KB rightX rightY rightZ refl refl refl r s h = trans (cong (HMap KB) s) r

compLlaw : {C : Cat}{M : Monad C}{X Y Z : ObjAdj M} → 
           (f :  HomAdj Y Z)(g : HomAdj X Y) →
           (K f ○ K g) ○ L (adj X) ≅ L (adj Z)
compLlaw {C}{M}{X}{Y}{Z} f g = 
  FunctorEq 
    _ 
    _
    (ext (λ A →
      trans (cong (OMap (K f)) (cong (λ F → OMap F A) (Llaw g)))
            (cong (λ F → OMap F A) (Llaw f))))
    (λ {A} {B} h → trans
      (HMaplem (cong (λ F → OMap F A) (Llaw g))
               (cong (λ F → OMap F B) (Llaw g)) 
               (cong (λ F → HMap F h) (Llaw g))
               (K f))
      (cong (λ F → HMap F h) (Llaw f)))

compRlaw : {C : Cat}{M : Monad C}{X Y Z : ObjAdj M} → 
           (f :  HomAdj Y Z)(g : HomAdj X Y) →
           R (adj X) ≅ R (adj Z) ○ (K f ○ K g)
compRlaw {C}{M}{X}{Y}{Z} f g = 
  FunctorEq 
    _ 
    _
    (ext (λ A →
      trans (cong (λ F → OMap F A) (Rlaw g))
            (cong (λ F → OMap F (OMap (K g) A)) (Rlaw f))))
    (λ {A} {B} h →
      trans (cong (λ F → HMap F h) (Rlaw g))
            (cong (λ F → HMap F (HMap (K g) h)) (Rlaw f)))

comprightlaw : {C : Cat}{M : Monad C}{X Y Z : ObjAdj M} → 
               (f :  HomAdj Y Z)(g : HomAdj X Y) →
               {X₁ : Obj C}{Y₁ : Obj (D X)}
               {f₁ : Hom C X₁ (OMap (R (adj X)) Y₁)} →
               HMap (K f ○ K g) (right (adj X) f₁) 
               ≅
               right (adj Z)
                     (subst (Hom C X₁) 
                            (fcong Y₁ (cong OMap (compRlaw f g))) 
                            f₁)
comprightlaw {C}{M}{X}{Y}{Z} f g {A}{B}{h} = 
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

compHomAdj : {C : Cat}{M : Monad C}{X Y Z : ObjAdj M} → 
             HomAdj Y Z → HomAdj X Y → HomAdj X Z
compHomAdj {C}{M}{X}{Y}{Z} f g = record {
    K        = K f ○ K g;
    Llaw     = compLlaw f g;
    Rlaw     = compRlaw f g;
    rightlaw = comprightlaw f g}

idlHomAdj : ∀{C}{M : Monad C}{X : ObjAdj M} {Y : ObjAdj M} {f : HomAdj X Y} → 
            compHomAdj idHomAdj f ≅ f
idlHomAdj {C}{M}{X}{Y}{f} = 
  HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))

idrHomAdj : ∀{C}{M : Monad C}{X : ObjAdj M}{Y : ObjAdj M}{f : HomAdj X Y} → 
            compHomAdj f idHomAdj ≅ f
idrHomAdj {C}{M}{X}{Y}{f} = 
  HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))

assHomAdj : ∀{C}{M : Monad C}
            {W : ObjAdj M}{X : ObjAdj M}{Y : ObjAdj M}{Z : ObjAdj M}
            {f : HomAdj Y Z} {g : HomAdj X Y} {h : HomAdj W X} →
            compHomAdj (compHomAdj f g) h ≅ compHomAdj f (compHomAdj g h)
assHomAdj {C}{M}{W}{X}{Y}{Z}{f}{g}{h} = 
  HomAdjEq _ _ (FunctorEq _ _ refl (λ h → refl))

CatofAdj : {C : Cat}(M : Monad C) → Cat
CatofAdj {C} M = record{
  Obj  = ObjAdj M;
  Hom  = HomAdj;
  iden = idHomAdj;
  comp = compHomAdj;
  idl  = idlHomAdj;
  idr  = idrHomAdj;
  ass  = λ{W X Y Z f g h} → assHomAdj {_}{_}{W}{X}{Y}{Z}{f}{g}{h}}

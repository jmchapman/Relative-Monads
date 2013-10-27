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
        law : R adj ○ L adj ≅ T M
open ObjAdj

record HomAdj {C : Cat}{M : Monad C}(A B : ObjAdj M) : Set where
  field K : Fun (D A) (D B)
        Llaw : K ○ L (adj A) ≅ L (adj B)
        Rlaw : R (adj A) ≅ R (adj B) ○ K
        rightlaw : ∀{X}{Y}{k : Hom C X (OMap (R (adj A)) Y)} → HMap K (right (adj A) k) ≅ right (adj B) (subst (λ Y → Hom C X Y) (fcong Y (cong OMap Rlaw)) {!kk!})

open HomAdj

HomAdjEq : {C : Cat}{M : Monad C}{A B : ObjAdj M}(f g : HomAdj A B) → K f ≅ K g → f ≅ g
HomAdjEq {C}{M}{A}{B} f g p = funnycong4 
  {Fun (D A) (D B)}
  {λ K → K ○ L (adj A) ≅ L (adj B)}
  {λ K _ → R (adj A) ≅ R (adj B) ○ K}
  {λ K _ Rlaw → ∀{X}{Y}{k : Hom C X (OMap (R (adj A)) Y)} → HMap K (right (adj A) k) ≅ right (adj B) (subst (λ Y → Hom C X Y) (fcong Y (cong OMap Rlaw)) k)}
  {HomAdj {C}{M} A B}
  (λ w x y z → record{K = w;Llaw = x;Rlaw = y;rightlaw = z})
  p 
  (fixtypes (FunctorEq _
                       _
                       (ext λ X → cong (λ F → OMap F (OMap (L (adj A)) X)) p)
                       (λ {X}{Y} h → cong (λ F → HMap F (HMap (L (adj A)) h)) p))
            refl)
   (fixtypes refl
             (FunctorEq _
                        _
                        (ext λ X → cong (λ F → OMap (R (adj B)) (OMap F X)) p)
                        (λ {X}{Y} h → cong (λ F → HMap (R (adj B)) (HMap F h)) p)))
   (iext (λ X → iext (λ Y → iext (λ k → fixtypes (cong (λ F → HMap F (right (adj A) k)) p) 
     (dcong (trans (stripsubst (Hom C X) k (fcong Y (cong OMap (Rlaw f)))) (sym (stripsubst (Hom C X) k (fcong Y (cong OMap (Rlaw g))))) ) 
            (cong (λ F → Hom (D B) (OMap (L (adj B)) X) (OMap F Y)) p)
            (icong (λ {Y} → right (adj B) {X}{Y}) (cong (λ F → OMap F Y) p)))))))

idHomAdj : {C : Cat}{M : Monad C}{X : ObjAdj M} → HomAdj X X
idHomAdj {C}{M}{X} = record {
    K = IdF (D X);
    Llaw = FunctorEq _ _ refl (λ _ → refl);
    Rlaw = FunctorEq _ _ refl (λ _ → refl);
    rightlaw = λ {A}{B}{k} → {!!}}

HMaplem : ∀{C D}{X X' Y Y' : Obj C} → X ≅ X' → Y ≅ Y' → {f : Hom C X Y}{f' : Hom C X' Y'} → f ≅ f' → (F : Fun C D) → 
          HMap F {X}{Y} f ≅ HMap F {X'}{Y'} f'
HMaplem refl refl refl F = refl

compHomAdj : {C : Cat}{M : Monad C}{X Y Z : ObjAdj M} → HomAdj Y Z → HomAdj X Y → HomAdj X Z
compHomAdj {C}{M}{X}{Y}{Z} f g = record {
    K    = K f ○ K g;
    Llaw = FunctorEq _
                     _
                     (ext λ A → trans (cong (OMap (K f)) (cong (λ F → OMap F A) (Llaw g))) (cong (λ F → OMap F A) (Llaw f)))
                     (λ {A}{B} h → trans (HMaplem (cong (λ F → OMap F A) (Llaw g)) 
                                                  (cong (λ F → OMap F B) (Llaw g)) 
                                         (cong (λ F → HMap F h) (Llaw g)) (K f)) (cong (λ F → HMap F h) (Llaw f)));
    Rlaw = FunctorEq _
                     _
                     (ext λ A → trans (cong (λ F → OMap F A) (Rlaw g)) (cong (λ F → OMap F (OMap (K g) A)) (Rlaw f)))
                     (λ {A}{B} h → trans (cong (λ F → HMap F h) (Rlaw g)) 

                                         (cong (λ F → HMap F (HMap (K g) h)) (Rlaw f)));
    rightlaw = {!!}}


{-
idlHomAdj : ∀{C}{M : Monad C}{X : ObjAdj M} {Y : ObjAdj M} {f : HomAdj X Y} → compHomAdj idHomAdj f ≅ f
idlHomAdj {C}{M}{X}{Y}{f} = HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))


idrHomAdj : ∀{C}{M : Monad C}{X : ObjAdj M}{Y : ObjAdj M}{f : HomAdj X Y} → compHomAdj f idHomAdj ≅ f
idrHomAdj {C}{M}{X}{Y}{f} = HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))


assHomAdj : ∀{C}{M : Monad C}{W : ObjAdj M}{X : ObjAdj M}{Y : ObjAdj M}{Z : ObjAdj M}
            {f : HomAdj Y Z} {g : HomAdj X Y} {h : HomAdj W X} →
            compHomAdj (compHomAdj f g) h ≅ compHomAdj f (compHomAdj g h)
assHomAdj {C}{M}{W}{X}{Y}{Z}{f}{g}{h} = HomAdjEq _ _ (FunctorEq _ _ refl (λ h → refl))


CatofAdj : {C : Cat}(M : Monad C) → Cat
CatofAdj {C} M = record{
  Obj  = ObjAdj M;
  Hom  = HomAdj;
  iden = idHomAdj;
  comp = compHomAdj;
  idl  = idlHomAdj;
  idr  = idrHomAdj;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → assHomAdj {C}{M}{W}{X}{Y}{Z}{f}{g}{h}}

-}

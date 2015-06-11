open import Monads
open import Categories

module Monads.CatofAdj {a b}{C : Cat {a}{b}}(M : Monad C) where

open import Library
open import Functors
open import Adjunctions

open Fun
open Monad M

open Cat

record ObjAdj {c d} : Set (a ⊔ b ⊔ lsuc c ⊔ lsuc d) where
  field D   : Cat {c}{d}
        adj : Adj C D
  open Adj adj
  field law : R ○ L ≅ TFun M
        ηlaw : ∀ {X} → left (iden D {OMap L X}) ≅ Monad.η M {X} 
        bindlaw : ∀{X Y}{f : Hom C X (T Y)} → 
          HMap R
               (right (subst (Hom C X) (fcong Y (cong OMap (sym law))) f)) 
          ≅ 
          Monad.bind M f

open ObjAdj

record HomAdj {c d}(A B : ObjAdj {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d) where
  constructor homadj
  open Adj
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

HomAdjEq : ∀{c d}{A B : ObjAdj {c}{d}}(f g : HomAdj A B) → K f ≅ K g → f ≅ g
HomAdjEq {A = A}{B = B} (homadj K Llaw Rlaw rightlaw) (homadj .K Llaw' Rlaw' rightlaw') refl =
  cong₃ (homadj K)
        (ir _ _)
        (ir _ _)
        (iext λ _ → iext λ _ → iext λ _ → hir refl)

rightlawlem : ∀{c d}{D : Cat {c}{d}}(R : Fun D C)(L : Fun C D)
  (p : OMap R ≅ OMap (R ○ (IdF D))) → 
  (right : {X : Obj C}{Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
           {Z : Obj C}{Y : Obj D}{f : Hom C Z (OMap R Y)} →
  right f ≅ right (subst (Hom C Z) (fcong Y p) f)
rightlawlem R L refl right = refl

idHomAdj : ∀{c d}{X : ObjAdj {c}{d}} → HomAdj X X
idHomAdj {X = X} = record {
    K = IdF (D X);
    Llaw = FunctorEq _ _ refl refl;
    Rlaw = FunctorEq _ _ refl refl;
    rightlaw = rightlawlem R
                           L
                           (cong OMap (FunctorEq R (R ○ IdF (D X)) refl refl)) 
                           right}
  where open Adj (adj X)

HMaplem : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{X X' Y Y' : Obj C} → 
          X ≅ X' → Y ≅ Y' → 
          {f : Hom C X Y}{f' : Hom C X' Y'} → f ≅ f' → (F : Fun C D) → 
          HMap F {X}{Y} f ≅ HMap F {X'}{Y'} f'
HMaplem refl refl refl F = refl

rightlawlem2 : ∀{c d e f g h}{D : Cat {c}{d}}{E : Cat {e}{f}}{F : Cat {g}{h}}
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
rightlawlem2 {D = D}{E = E}{F = F} 
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

compLlaw : ∀{c d}
           {X Y Z : ObjAdj {c}{d}}
           (f :  HomAdj Y Z)(g : HomAdj X Y) →
           (K f ○ K g) ○ Adj.L (ObjAdj.adj X) ≅ Adj.L (ObjAdj.adj Z)
compLlaw {X = X}{Y = Y}{Z = Z} f g = FunctorEq
  _
  _
  (ext λ A → 
    proof
    OMap (K f) (OMap (K g) (OMap (L (adj X)) A))
    ≅⟨ cong (λ F → OMap (K f) (OMap F A)) (Llaw g) ⟩ 
    OMap (K f) (OMap (L (adj Y)) A)
    ≅⟨ cong (λ F → OMap F A) (Llaw f) ⟩ 
    OMap (L (adj Z)) A
    ∎)
  (iext λ A → iext λ B → ext λ h →
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
  where open Adj

compRlaw : ∀{c d}{X Y Z : ObjAdj {c}{d}}
           (f :  HomAdj Y Z)(g : HomAdj X Y) →
           Adj.R (adj X) ≅ Adj.R (adj Z) ○ (K f ○ K g)
compRlaw {X = X}{Y = Y}{Z = Z} f g = FunctorEq 
    _ 
    _
    (ext λ A → proof
      OMap (R (adj X)) A 
      ≅⟨ cong (λ F → OMap F A) (Rlaw g) ⟩
      OMap (R (adj Y)) (OMap (K g) A)
      ≅⟨ cong (λ F → OMap F (OMap (K g) A)) (Rlaw f) ⟩
      OMap (R (adj Z)) (OMap (K f) (OMap (K g) A)) 
      ∎)
    (iext λ A → iext λ B → ext λ h →
      trans (cong (λ F → HMap F h) (Rlaw g))
            (cong (λ F → HMap F (HMap (K g) h)) (Rlaw f)))
    where open Adj

comprightlaw : ∀{c d}{X Y Z : ObjAdj {c}{d}}
               (f :  HomAdj Y Z)(g : HomAdj X Y) →
               {X₁ : Obj C}{Y₁ : Obj (D X)}
               {f₁ : Hom C X₁ (OMap (Adj.R (adj X)) Y₁)} →
               HMap (K f ○ K g) (Adj.right (adj X) f₁) 
               ≅
               Adj.right (adj Z)
                     (subst (Hom C X₁) 
                            (fcong Y₁ (cong OMap (compRlaw f g))) 
                            f₁)
comprightlaw {X = X}{Y = Y}{Z = Z} f g {A}{B}{h} = trans
  (rightlawlem2 (R (adj X)) (L (adj X)) (R (adj Y)) (L (adj Y))
                (R (adj Z)) (L (adj Z)) (K g) (K f) (right (adj X)) (right (adj Y))
                (right (adj Z)) (Rlaw f) (Rlaw g) (Llaw g) (rightlaw f)
                (rightlaw g) h)
  (cong (right (adj Z))
        (trans (stripsubst (Hom C A) h (fcong B (cong OMap (trans (Rlaw g) (cong (λ F → F ○ K g) (Rlaw f)))))) (sym (stripsubst (Hom C A) h (fcong B (cong OMap (compRlaw f g)))))))
  where open Adj

compHomAdj : ∀{c d}{X Y Z : ObjAdj {c}{d}} → 
             HomAdj Y Z → HomAdj X Y → HomAdj X Z
compHomAdj {X = X}{Y = Y}{Z = Z} f g = record {
    K        = K f ○ K g;
    Llaw     = compLlaw f g;
    Rlaw     = compRlaw f g;
    rightlaw = comprightlaw f g}


idlHomAdj : ∀{c d}{X Y : ObjAdj {c}{d}}{f : HomAdj X Y} → 
            compHomAdj idHomAdj f ≅ f
idlHomAdj{X = X}{Y = Y}{f = f} = 
  HomAdjEq _ _ (FunctorEq _ _ refl refl)


idrHomAdj : ∀{c d}{X Y : ObjAdj {c}{d}}{f : HomAdj X Y} → 
            compHomAdj f idHomAdj ≅ f
idrHomAdj {X = X}{Y = Y}{f = f} = 
  HomAdjEq _ _ (FunctorEq _ _ refl refl)

assHomAdj : ∀{c d}{W X Y Z : ObjAdj {c}{d}}
            {f : HomAdj Y Z} {g : HomAdj X Y} {h : HomAdj W X} →
            compHomAdj (compHomAdj f g) h ≅ compHomAdj f (compHomAdj g h)
assHomAdj {W = W}{X = X}{Y = Y}{Z = Z}{f = f}{g = g}{h = h} = 
  HomAdjEq _ _ (FunctorEq _ _ refl refl)

CatofAdj : ∀{c d} → Cat
CatofAdj {c}{d} = record {
         Obj  = ObjAdj {c}{d};
  Hom  = HomAdj;
  iden = idHomAdj;
  comp = compHomAdj;
  idl  = idlHomAdj;
  idr  = idrHomAdj;
  ass  = λ{W X Y Z f g h} → assHomAdj {W = W}{X}{Y}{Z}{f}{g}{h}}
-- -}

open import Categories
open import Monads

module Monads.CatofAdj.InitAdj {a b}{C : Cat {a}{b} }(M : Monad C) where

open import Library
open import Functors
open import Naturals
open import Adjunctions
open import Monads.CatofAdj M
open import Categories.Initial
open import Monads.Kleisli M
open import Monads.Kleisli.Functors M
open import Monads.Kleisli.Adjunction M
open import Adjunctions.Adj2Mon

open Cat
open Fun
open Monad M
open NatT
open Adj

lemX : R KlAdj ○ L KlAdj ≅ TFun M
lemX = FunctorEq _ _ refl (λ f → refl) 

KlObj : Obj CatofAdj
KlObj = record { 
  D   = Kl; 
  adj = KlAdj; 
  law = lemX;
  ηlaw = refl;
  bindlaw = λ{X}{Y}{f} → 
    cong bind
         (stripsubst (Hom C X) f (fcong Y (cong OMap (sym lemX))))}

open ObjAdj
open import Isomorphism
open Iso

lemZ : {D : Cat {a}{b}}{F G G' : Fun C D} → 
       G ≅ G' → {α : NatT F G}{β : NatT F G'} → α ≅ β → 
       ∀ {X} → cmp α {X} ≅ cmp β {X}
lemZ refl refl = refl

lemZ' : {D : Cat {a}{b}}{F F' G G' : Fun C D} → 
        F ≅ F' → G ≅ G' → {α : NatT F G}{β : NatT F' G'} → α ≅ β → 
        ∀ {X} → cmp α {X} ≅ cmp β {X}
lemZ' refl refl refl = refl


lemfid : {D : Cat {a}{b}}(L : Fun C D)(R : Fun D C)(T : Fun C C) 
  (p : T ≅ R ○ L) (η : ∀ {X} → Hom C X (OMap T X))
  (right : {X : Obj C}{Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
  (left : {X : Obj C}{Y : Obj D} → Hom D (OMap L X) Y → Hom C X (OMap R Y)) → 
  (q :  {X : Obj C}{Y : Obj D}(f : Hom D (OMap L X) Y) → right (left f) ≅ f) → 
  (r : {X : Obj C} → left (iden D {OMap L X}) ≅ η {X}) → 
  {X : Obj C} → 
    right (subst (Hom C X) (fcong X (cong OMap p)) η) 
    ≅ 
    iden D {OMap L X}
lemfid {D = D} L R .(R ○ L) refl η right left q r {X} = 
  trans (cong right (sym r)) (q (iden D))

lemfcomp : {D : Cat {a}{b}}(L : Fun C D)(R : Fun D C)(T : Fun C C) 
  (p : T ≅ R ○ L)
  (bind : ∀{X Y} → Hom C X (OMap T Y) → Hom C (OMap T X) (OMap T Y)) →
  (right : {X : Obj C} {Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
  (q : {X Y : Obj C} {f : Hom C X (OMap T Y)} → 
       HMap R (right (subst (Hom C X) (fcong Y (cong OMap p)) f)) ≅ bind f) → 
  (r : {X X' : Obj C}{Y Y' : Obj D}
       (f : Hom C X' X)(g : Hom D Y Y')
       (h : Hom C X (OMap R Y)) → 
       right (comp C (HMap R g) (comp C h f)) 
       ≅ 
       comp D g (comp D (right h) (HMap L f))) → 
  ∀{X Y Z : Obj C} {f : Hom C Y (OMap T Z)} {g : Hom C X (OMap T Y)} →
    right (subst (Hom C X) (fcong Z (cong OMap p)) (comp C (bind f) g))
    ≅
    comp D (right (subst (Hom C Y) (fcong Z (cong OMap p)) f))
           (right (subst (Hom C X) (fcong Y (cong OMap p)) g))
lemfcomp {D = D} L R .(R ○ L) refl bind right q r {X}{Y}{Z}{f}{g} = 
  trans (cong₂ (λ f g → right (comp C f g)) (sym (q {f = f})) (sym (idr C)))
        (trans (r (iden C) (right f) g) 
               (cong (comp D (right f)) 
                     (trans (cong (comp D (right g)) (fid L)) (idr D))))


lemLlaw : {D : Cat {a}{b}}(L : Fun C D)(R : Fun D C)(T : Fun C C) 
          (p : T ≅ R ○ L) (η : ∀ {X} → Hom C X (OMap T X)) → 
          (right : {X : Obj C} {Y : Obj D} → 
                   Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
          (left : {X : Obj C} {Y : Obj D} → 
                  Hom D (OMap L X) Y → Hom C X (OMap R Y)) → 
          (q : {X : Obj C} {Y : Obj D} (f : Hom D (OMap L X) Y) →
               right (left f) ≅ f) → 
          (r : {X : Obj C} → left (iden D {OMap L X}) ≅ η {X}) → 
          (t : {X X' : Obj C}{Y Y' : Obj D}
                   (f : Hom C X' X)(g : Hom D Y Y')
                   (h : Hom C X (OMap R Y)) → 
                   right (comp C (HMap R g) (comp C h f)) 
                   ≅ 
                   comp D g (comp D (right h) (HMap L f)) ) → 
          {X Y : Obj C} (f : Hom C X Y) →
          right (subst (Hom C X) (fcong Y (cong OMap p))  (comp C η f)) 
          ≅ 
          HMap L f
lemLlaw {D = D} L R .(R ○ L) refl η right left q r t {X}{Y} f = 
  trans (cong (λ g → right (comp C g f)) (sym r)) 
        (trans (trans (trans (cong right 
                                   (trans (sym (idl C)) 
                                          (cong (λ g → comp C g 
                                                   (comp C (left (iden D)) f)) 
                                                (sym (fid R)))))
                             (t f (iden D) (left (iden D)))) 
                      (cong (comp D (iden D)) 
                            (trans (cong (λ g → comp D g (HMap L f)) 
                                         (q (iden D))) 
                                   (idl D))))
               (idl D))

K' : (A : Obj CatofAdj) → Fun (D KlObj) (D A)
K' A = record {
                 OMap = OMap (L (adj A));
                 HMap =
                   λ {X} {Y} f →
                     right (adj A)
                     (subst (Hom C X) (fcong Y (cong OMap (sym (law A)))) f);
                 fid =
                   lemfid (L (adj A)) (R (adj A)) (TFun M) (sym (law A)) η
                   (right (adj A)) (left (adj A)) (lawa (adj A)) (ηlaw A);
                 fcomp =
                   lemfcomp (L (adj A)) 
                            (R (adj A)) 
                            (TFun M) 
                            (sym (law A)) 
                            bind
                            (right (adj A)) 
                            (bindlaw A) 
                            (natright (adj A)) }

Llaw' : (A : Obj CatofAdj) → K' A ○ L (adj KlObj) ≅ L (adj A)
Llaw' A = FunctorEq 
  _ 
  _ 
  refl
  (lemLlaw (L (adj A)) 
           (R (adj A)) 
           (TFun M) 
           (sym (law A)) 
           η
           (right (adj A)) 
           (left (adj A)) 
           (lawa (adj A)) 
           (ηlaw A)
           (natright (adj A)))

Rlaw' : (A : Obj CatofAdj) → R (adj KlObj) ≅ R (adj A) ○ K' A
Rlaw' A = FunctorEq 
  _ 
  _ 
  (cong OMap (sym (law A))) (λ f → sym (bindlaw A))

rightlaw' : (A : Obj CatofAdj) → 
            {X : Obj C} {Y : Obj (D KlObj)}
            {f : Hom C X (OMap (R (adj KlObj)) Y)} →
            HMap (K' A) (right (adj KlObj) f) ≅
            right (adj A) (subst (Hom C X) (fcong Y (cong OMap (Rlaw' A))) f)
rightlaw' A {X}{Y}{f} = 
  cong (right (adj A))
       (trans (stripsubst (Hom C X) f (fcong Y (cong OMap (sym (law A)))))
              (sym (stripsubst (Hom C X) 
                               f
                               (fcong Y
                                      (cong OMap
                                            (FunctorEq 
                                              _ 
                                              _ 
                                              (cong OMap (sym (law A)))
                                              (λ _ → sym (bindlaw A))))))))

KlHom : {A : Obj CatofAdj} → Hom CatofAdj KlObj A
KlHom {A} = record { 
  K        = K' A; 
  Llaw     = Llaw' A; 
  Rlaw     = Rlaw' A; 
  rightlaw = rightlaw' A }

uniq : {X : Obj CatofAdj}{f : Hom CatofAdj KlObj X} → KlHom ≅ f
uniq {X}{V} = HomAdjEq 
  _ 
  _
  (FunctorEq 
    _ 
    _ 
    (cong OMap (sym (HomAdj.Llaw V))) 
    (λ {A} {B} f → trans (cong₂ (λ B₁ → right (adj X) {A} {B₁})
                                (sym (fcong B (cong OMap (HomAdj.Llaw V))))
                                (trans (stripsubst 
                                         (Hom C A) 
                                         f 
                                         (fcong B (cong OMap (sym (law X)))))
                                       (sym (stripsubst 
                                              (Hom C A) 
                                              f 
                                              (fcong 
                                                B 
                                                (cong OMap (HomAdj.Rlaw V)))))))
                         (sym (HomAdj.rightlaw V))))


KlIsInit : Init CatofAdj
KlIsInit = record { 
  I   = KlObj;
  i   = KlHom;
  law = uniq}

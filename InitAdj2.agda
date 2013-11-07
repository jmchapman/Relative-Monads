module InitAdj2 where

open import Monads2
open import Functors
open import Naturals
open import Adjunctions2
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import CatofAdj2
open import Initial
open import Kleisli2
open import KleisliFunctors2
open import KleisliAdj2
open import Adj2Mon2

open Cat
open Fun
open Monad
open NatT
open Adj

lemX : ∀{C}(M : Monad C) → R (KlAdj M) ○ L (KlAdj M) ≅ TFun M
lemX {C} M = FunctorEq _ _ refl (λ f → refl) 

KlObj : {C : Cat}(M : Monad C) → 
        Obj (CatofAdj M)
KlObj {C} M = record { 
  D   = Kl M; 
  adj = KlAdj M; 
  law = lemX M;
  ηlaw = refl;
  bindlaw = λ{X}{Y}{f} → cong (bind M) (stripsubst (Hom C X) f (fcong Y (cong OMap (sym (lemX M)))))}

open ObjAdj
open import Isomorphism
open Iso

lemZ : ∀{C}{D}{F G G' : Fun C D} → G ≅ G' → {α : NatT F G}{β : NatT F G'} → α ≅ β → 
       ∀ {X} → cmp α {X} ≅ cmp β {X}
lemZ refl refl = refl

lemZ' : ∀{C}{D}{F F' G G' : Fun C D} → F ≅ F' → G ≅ G' → {α : NatT F G}{β : NatT F' G'} → α ≅ β → 
       ∀ {X} → cmp α {X} ≅ cmp β {X}
lemZ' refl refl refl = refl


lemfid : ∀{C D}(L : Fun C D)(R : Fun D C)(T : Fun C C) (p : T ≅ R ○ L) (η : ∀ {X} → Hom C X (OMap T X))
  (right : {X : Obj C} {Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
  (left : {X : Obj C} {Y : Obj D} → Hom D (OMap L X) Y → Hom C X (OMap R Y)) → 
  (q :  {X : Obj C} {Y : Obj D} (f : Hom D (OMap L X) Y) → right (left f) ≅ f) → 
  (r : {X : Obj C} → left (iden D {OMap L X}) ≅ η {X}) → 
  {X : Obj C} → right (subst (Hom C X) (fcong X (cong OMap p)) η) ≅ iden D {OMap L X}
lemfid {C}{D} L R .(R ○ L) refl η right left q r {X} = trans (cong right (sym r)) (q (iden D))

lemfcomp : ∀{C D}(L : Fun C D)(R : Fun D C)(T : Fun C C) (p : T ≅ R ○ L)(bind : ∀{X Y} → Hom C X (OMap T Y) → Hom C (OMap T X) (OMap T Y)) →
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
lemfcomp {C}{D} L R .(R ○ L) refl bind right q r {X}{Y}{Z}{f}{g} = 
  trans (cong₂ (λ f g → right (comp C f g)) (sym (q {f = f})) (sym (idr C))) 
        (trans (r (iden C) (right f) g) (cong (comp D (right f)) (trans (cong (comp D (right g)) (fid L)) (idr D))))


lemLlaw : ∀{C D}(L : Fun C D)(R : Fun D C)(T : Fun C C) (p : T ≅ R ○ L) (η : ∀ {X} → Hom C X (OMap T X)) → 
          (right : {X : Obj C} {Y : Obj D} → Hom C X (OMap R Y) → Hom D (OMap L X) Y) →
          (left : {X : Obj C} {Y : Obj D} → Hom D (OMap L X) Y → Hom C X (OMap R Y)) → 
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
          right (subst (Hom C X) (fcong Y (cong OMap p))  (comp C η f)) ≅ HMap L f
lemLlaw {C}{D} L R .(R ○ L) refl η right left q r t {X}{Y} f = 
  trans (cong (λ g → right (comp C g f)) (sym r)) 
        (trans (trans (trans (cong right (trans (sym (idl C)) (cong (λ g → comp C g (comp C (left (iden D)) f)) (sym (fid R)))))
                             (t f (iden D) (left (iden D)))) 
                      (cong (comp D (iden D)) (trans (cong (λ g → comp D g (HMap L f)) (q (iden D))) (idl D)))) 
               (idl D))

K' : ∀{C}(M : Monad C)(A : Obj (CatofAdj M)) → Fun (D (KlObj M)) (D A)
K' {C} M A = record {
                 OMap = OMap (L (adj A));
                 HMap =
                   λ {X} {Y} f →
                     right (adj A)
                     (subst (Hom C X) (fcong Y (cong OMap (sym (law A)))) f);
                 fid =
                   lemfid (L (adj A)) (R (adj A)) (TFun M) (sym (law A)) (η M)
                   (right (adj A)) (left (adj A)) (lawa (adj A)) (ηlaw A);
                 fcomp =
                   lemfcomp (L (adj A)) (R (adj A)) (TFun M) (sym (law A)) (bind M)
                   (right (adj A)) (bindlaw A) (natright (adj A)) }

Llaw' : ∀{C}(M : Monad C)(A : Obj (CatofAdj M)) → 
        K' M A ○ L (adj (KlObj M)) ≅ L (adj A)
Llaw' {C} M A = FunctorEq _ _ refl
                  (lemLlaw (L (adj A)) (R (adj A)) (TFun M) (sym (law A)) (η M)
                   (right (adj A)) (left (adj A)) (lawa (adj A)) (ηlaw A)
                   (natright (adj A)))

Rlaw' : ∀{C}(M : Monad C)(A : Obj (CatofAdj M)) → 
        R (adj (KlObj M)) ≅ R (adj A) ○ K' M A
Rlaw' {C} M A = FunctorEq _ _ (cong OMap (sym (law A))) (λ f → sym (bindlaw A))

rightlaw' : ∀{C}(M : Monad C)(A : Obj (CatofAdj M)) → 
            {X : Obj C} {Y : Obj (D (KlObj M))}
            {f : Hom C X (OMap (R (adj (KlObj M))) Y)} →
            HMap (K' M A) (right (adj (KlObj M)) f) ≅
            right (adj A) (subst (Hom C X) (fcong Y (cong OMap (Rlaw' M A))) f)
rightlaw' {C} M A {X}{Y}{f} = cong (right (adj A))
                                (trans (stripsubst (Hom C X) f (fcong Y (cong OMap (sym (law A)))))
                                 (sym
                                  (stripsubst (Hom C X) f
                                   (fcong Y
                                    (cong OMap
                                     (FunctorEq _ _ (cong OMap (sym (law A)))
                                      (λ f₁ → sym (bindlaw A))))))))

KlHom : ∀{C}(M : Monad C){A : Obj (CatofAdj M)} → Hom (CatofAdj M) (KlObj M) A
KlHom {C} M {A} = record { 
  K        = K' M A; 
  Llaw     = Llaw' M A; 
  Rlaw     = Rlaw' M A; 
  rightlaw = rightlaw' M A }



uniq : {C : Cat}(M : Monad C) → 
       {X : Obj (CatofAdj M)}{f : Hom (CatofAdj M) (KlObj M) X} → KlHom M ≅ f
uniq {C} M {X}{V} = HomAdjEq _ 
                 _
                 (FunctorEq _ 
                            _ 
                            (cong OMap (sym (HomAdj.Llaw V))) 
                            (λ {A} {B} f → trans (cong₂ (λ B₁ → right (adj X) {A} {B₁}) 
                                                        (sym (fcong B (cong OMap (HomAdj.Llaw V))))
                                                        (trans (stripsubst (Hom C A) f (fcong B (cong OMap (sym (law X)))))
                                                               (sym (stripsubst (Hom C A) f (fcong B (cong OMap (HomAdj.Rlaw V))))))) 
                                                 (sym (HomAdj.rightlaw V))))


KlIsInit : {C : Cat}(M : Monad C) → Init (CatofAdj M)
KlIsInit {C} M = record { 
  I   = KlObj M;
  i   = KlHom M;
  law = uniq M}

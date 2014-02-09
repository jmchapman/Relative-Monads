open import Categories
open import Functors
open import RMonads

module RMonads.CatofRAdj {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
                         (M : RMonad J) where

open import Library

open import RAdjunctions

open Fun
open Cat


record ObjAdj {e f} : Set ((a ⊔ b ⊔ c ⊔ d ⊔ lsuc e ⊔ lsuc f)) where
  open RMonad M
  field E   : Cat {e}{f}
        adj : RAdj J E
  open RAdj adj
  field law : R ○ L ≅ TFun M
        ηlaw : ∀{X} → left (iden E {OMap L X}) ≅ η {X}
        bindlaw : ∀{X Y}{f : Hom D (OMap J X) (T Y)} → 
          HMap R (right (subst (Hom D (OMap J X)) 
                               (fcong Y (cong OMap (sym law))) f)) 
          ≅ bind f 
open ObjAdj

record HomAdj {e f}(A B : ObjAdj {e}{f}) : Set (a ⊔ b ⊔ c ⊔ d ⊔ lsuc (e ⊔ f))
  where
  open RAdj
  field K : Fun (E A) (E B)
        Llaw : K ○ L (adj A) ≅ L (adj B)  
        Rlaw : R (adj A) ≅ R (adj B) ○ K
        rightlaw : {X : Obj C}{Y : Obj (E A)}
                   {f : Hom D (OMap J X) (OMap (R (adj A)) Y)} →  
                   HMap K (right (adj A) {X}{Y} f) 
                   ≅ 
                   right (adj B)
                         {X}
                         {OMap K Y}
                         (subst (Hom D (OMap J X)) 
                                (fcong Y (cong OMap Rlaw)) 
                                f)

open HomAdj

HomAdjEq : ∀{a b}{A B : ObjAdj {a}{b}}
           (f g : HomAdj A B) → K f ≅ K g → f ≅ g
HomAdjEq {A = A}{B = B} f g p = funnycong4
  {A = Fun (E A) (E B)}
  {B = λ K → K ○ L (adj A) ≅ L (adj B)}
  {C = λ K Llaw → R (adj A) ≅ R (adj B) ○ K}
  {D = λ K Llaw Rlaw → {X : Obj C}
                   {Y : Obj (E A)}
                   {f : Hom D (OMap J X) (OMap (R (adj A)) Y)} →  
  HMap K (right (adj A) {X}{Y} f) 
  ≅ 
  right (adj B)
        {X}
        {OMap K Y}
        (subst (Hom D (OMap J X)) (fcong Y (cong OMap Rlaw)) f)}
  {HomAdj A B}
  (λ x y z z' → record{K = x;Llaw = y;Rlaw = z; rightlaw = z'})
  p 
  (fixtypes (sym (Llaw g)))
  (fixtypes (sym (Rlaw f))) 
  (iext λ X → iext λ Y → iext λ h → fixtypes 
    (trans (sym (rightlaw f)) 
           (cong (λ F → HMap F (right (adj A) h)) p)))
  where open RAdj

rightlawlem : ∀{e f}{E : Cat {e}{f}}(R : Fun E D)(L : Fun C E) → 
  (p : OMap R ≅ OMap (R ○ (IdF E))) → 
  (right : {X : Obj C} {Y : Obj E} → 
           Hom D (OMap J X) (OMap R Y) → Hom E (OMap L X) Y) →
  {X : Obj C}{Y : Obj E}{f : Hom D (OMap J X) (OMap R Y)} →
  right f ≅ right (subst (Hom D (OMap J X)) (fcong Y p) f)
rightlawlem R L refl right {X}{Y}{f} = refl

idLlaw : ∀{e f}(X : ObjAdj {e}{f}) → 
         IdF (E X) ○ RAdj.L (adj X) ≅ RAdj.L (adj X)
idLlaw X = FunctorEq _ _ refl (λ _ → refl)

idRlaw : ∀{e f}(X : ObjAdj {e}{f}) → 
         RAdj.R (adj X) ≅ RAdj.R (adj X) ○ IdF (E X)
idRlaw X  = FunctorEq _ _ refl (λ _ → refl)

idrightlaw : ∀{e f}
             (X : ObjAdj {e}{f}) → 
             {X₁ : Obj C} {Y : Obj (E X)}
             {f : Hom D (OMap J X₁) (OMap (RAdj.R (adj X)) Y)} →
             HMap (IdF (E X)) (RAdj.right (adj X) f) 
             ≅ 
             RAdj.right (adj X) 
                        (subst (Hom D (OMap J X₁)) 
                               (fcong Y (cong OMap (idRlaw X))) 
                               f)
idrightlaw X {X₁}{Y}{f} = 
  rightlawlem (R (adj X)) 
              (L (adj X)) 
              (cong OMap (FunctorEq _ _ refl (λ _ → refl)))  
              (right (adj X)) 
  where open RAdj

idHomAdj : ∀{e f}{X : ObjAdj {e}{f}} → HomAdj X X
idHomAdj {X = X} = record { 
  K        = IdF (E X); 
  Llaw     = idLlaw X; 
  Rlaw     = idRlaw X; 
  rightlaw = idrightlaw X }

HMaplem : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{X X' Y Y' : Obj C} → 
          X ≅ X' → Y ≅ Y' → 
          {f : Hom C X Y}{f' : Hom C X' Y'} → f ≅ f' → (F : Fun C D) → 
          HMap F {X}{Y} f ≅ HMap F {X'}{Y'} f'
HMaplem refl refl refl F = refl

rightlawlem2 : ∀{e f g h i j}{E : Cat {e}{f}}{F : Cat {g}{h}}{G : Cat {i}{j}}
  (J : Fun C D)
  (RX : Fun E D)(LX : Fun C E)
  (RY : Fun F D)(LY : Fun C F)
  (RZ : Fun G D)(LZ : Fun C G)
  (KA : Fun E F)(KB : Fun F G) → 
  (rightX : {X : Obj C}{Y : Obj E} → 
            Hom D (OMap J X) (OMap RX Y) → Hom E (OMap LX X) Y)
  (rightY : {X : Obj C}{Y : Obj F} → 
            Hom D (OMap J X) (OMap RY Y) → Hom F (OMap LY X) Y)
  (rightZ : {X : Obj C}{Y : Obj G} → 
            Hom D (OMap J X) (OMap RZ Y) → Hom G (OMap LZ X) Y) → 
  (p : RY ≅ RZ ○ KB)(q : RX ≅ RY ○ KA) →
  (p' : KA ○ LX ≅ LY) → 
  (r : {X : Obj C}{Y : Obj F}{f : Hom D (OMap J X) (OMap RY Y)} →
       HMap KB (rightY f) 
       ≅ 
       rightZ (subst (Hom D (OMap J X)) 
                     (fcong Y (cong OMap p)) 
                     f)) →
  (s : {X : Obj C}{Y : Obj E}{f : Hom D (OMap J X) (OMap RX Y)} →
       HMap KA (rightX f) 
       ≅ 
       rightY (subst (Hom D (OMap J X)) 
                     (fcong Y (cong OMap q)) 
                     f)) →
  ∀{A B}(h : Hom D (OMap J A) (OMap RX B)) → 
  HMap (KB ○ KA) (rightX h) ≅
  rightZ
  (subst (Hom D (OMap J A)) 
         (fcong B (cong OMap (trans q (cong (λ F₁ → F₁ ○ KA) p)))) 
         h)
rightlawlem2 J .((RZ ○ KB) ○ KA) LX .(RZ ○ KB) .(KA ○ LX) RZ LZ KA KB 
  rightX rightY rightZ refl refl refl r s h = trans (cong (HMap KB) s) r

compLlaw : ∀{e f}{X Y Z : ObjAdj {e}{f}} → 
            (f : HomAdj Y Z)(g : HomAdj X Y) →
            (K f ○ K g) ○ RAdj.L (adj X) ≅ RAdj.L (adj Z)
compLlaw {X = X}{Y = Y}{Z = Z} f g = FunctorEq 
  _ 
  _
  (ext (λ A → trans 
    (cong (OMap (K f)) (cong (λ F → OMap F A) (Llaw g)))
    (cong (λ F → OMap F A) (Llaw f))))
  (λ {A} {B} h → trans 
    (HMaplem 
      (cong (λ F → OMap F A) (Llaw g)) 
      (cong (λ F → OMap F B) (Llaw g)) 
      (cong (λ F → HMap F h) (Llaw g)) 
      (K f))
    (cong (λ F → HMap F h) (Llaw f)))

compRlaw : ∀{e f}{X Y Z : ObjAdj {e}{f}} → 
            (f : HomAdj Y Z)(g : HomAdj X Y) →
            RAdj.R (adj X) ≅ RAdj.R (adj Z) ○ (K f ○ K g)
compRlaw {X = X}{Y = Y}{Z = Z} f g = FunctorEq 
  _ 
  _
  (ext (λ A → trans 
    (cong (λ F → OMap F A) (Rlaw g))
    (cong (λ F → OMap F (OMap (K g) A)) (Rlaw f))))
  (λ {A} {B} h → trans 
    (cong (λ F → HMap F h) (Rlaw g))
    (cong (λ F → HMap F (HMap (K g) h)) (Rlaw f)))


comprightlaw : ∀{e f}{X Y Z : ObjAdj {e}{f}} → 
            (f : HomAdj Y Z)(g : HomAdj X Y) →
            {A : Obj C} {B : Obj (E X)}
            {h : Hom D (OMap J A) (OMap (RAdj.R (adj X)) B)} →
            HMap (K f ○ K g) (RAdj.right (adj X) h) 
            ≅
            RAdj.right (adj Z)
                       (subst (Hom D (OMap J A)) 
                              (fcong B (cong OMap (compRlaw f g)))
                              h)
comprightlaw {X = X}{Y = Y}{Z = Z} f g {A}{B}{h} = trans
  (rightlawlem2 J (R (adj X)) (L (adj X)) (R (adj Y)) (L (adj Y))
   (R (adj Z)) (L (adj Z)) (K g) (K f) (right (adj X)) (right (adj Y))
   (right (adj Z)) (Rlaw f) (Rlaw g) (Llaw g) (rightlaw f)
   (rightlaw g) h)
  (cong (right (adj Z))
   (trans
    (stripsubst (Hom D (OMap J A)) h
     (fcong B
      (cong OMap (trans (Rlaw g) (cong (λ F → F ○ K g) (Rlaw f))))))
    (sym
     (stripsubst (Hom D (OMap J A)) h
      (fcong B
       (cong OMap
        (FunctorEq (R (adj X)) _
         (ext
          (λ A₁ →
             trans (cong (λ F → OMap F A₁) (Rlaw g))
             (cong (λ F → OMap F (OMap (K g) A₁)) (Rlaw f))))
         (λ {A₁} {B₁} h₁ →
            trans (cong (λ F → HMap F h₁) (Rlaw g))
            (cong (λ F → HMap F (HMap (K g) h₁)) (Rlaw f))))))))))
    where open RAdj

compHomAdj : ∀{e f}{X Y Z : ObjAdj {e}{f}} → 
             HomAdj Y Z → HomAdj X Y → HomAdj X Z
compHomAdj {X = X}{Y = Y}{Z = Z} f g = record { 
  K        = K f ○ K g; 
  Llaw     = compLlaw f g;
  Rlaw     = compRlaw f g; 
  rightlaw = comprightlaw f g }

idlHomAdj : ∀{e f}{X Y : ObjAdj {e}{f}}
            {f : HomAdj X Y} → compHomAdj idHomAdj f ≅ f
idlHomAdj = HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))

idrHomAdj : ∀{e f}{X Y : ObjAdj {e}{f}}
            {f : HomAdj X Y} → compHomAdj f idHomAdj ≅ f
idrHomAdj  = HomAdjEq _ _ (FunctorEq _ _ refl (λ {X}{Y} h → refl))

assHomAdj : ∀{e f}{W X Y Z : ObjAdj {e}{f}}
            {f : HomAdj Y Z} {g : HomAdj X Y} {h : HomAdj W X} →
            compHomAdj (compHomAdj f g) h ≅ compHomAdj f (compHomAdj g h)
assHomAdj = HomAdjEq _ _ (FunctorEq _ _ refl (λ h → refl))

CatofAdj : ∀{e f} → Cat
CatofAdj {e}{f} = record{
  Obj  = ObjAdj {e}{f};
  Hom  = HomAdj;
  iden = idHomAdj;
  comp = compHomAdj;
  idl  = idlHomAdj;
  idr  = idrHomAdj;
  ass  = λ{W X Y Z f g h} → 
    assHomAdj {W = W}{X = X}{Y = Y}{Z = Z}{f = f}{g = g}{h = h}}


{-# OPTIONS --type-in-type #-}
open import RMonads
open import Functors
open import Categories
import RMonads.CatofRAdj

module RMonads.CatofRAdj.TermRAdjHom 
  {C D}
  {J : Fun C D}
  (M : RMonad J)
  (A : Cat.Obj (RMonads.CatofRAdj.CatofAdj M))
  where

open import Library
open import RAdjunctions
open RMonads.CatofRAdj M
open import Categories.Terminal
open import RMonads.REM M
open import RMonads.REM.Adjunction
open import RAdjunctions.RAdj2RMon
open import RMonads.CatofRAdj.TermRAdjObj M

open Cat
open Fun
open RAdj
open RMonad M

alaw1lem : ∀{E}(T : Fun C D)(L : Fun C E)(R : Fun E D)
  (p : R ○ L ≅ T)
  (η : ∀ {X} → Hom D (OMap J X) (OMap T X)) → 
  (right : ∀ {X Y} → Hom D (OMap J X) (OMap R Y) → Hom E (OMap L X) Y) → 
  (left : ∀ {X Y} → Hom E (OMap L X) Y → Hom D (OMap J X) (OMap R Y)) → 
  (ηlaw : ∀ {X} → left (iden E {OMap L X}) ≅ η {X}) → 
  ∀ {X}{Z}{f : Hom D (OMap J Z) (OMap R X)} → 
  (nat : comp D (HMap R (right f)) (comp D (left (iden E)) (HMap J (iden C)))
         ≅
         left (comp E (right f) (comp E (iden E) (HMap L (iden C))))) →
  (lawb : left (right f) ≅ f) → 
  f 
  ≅
  comp D (subst (λ Z → Hom D Z (OMap R X)) 
                (fcong Z (cong OMap p))
                (HMap R (right f))) 
         η
alaw1lem {E} .(R ○ L) L R refl η right left ηlaw {X}{Z}{f} nat lawb = 
  trans (trans (trans (sym lawb) 
                      (cong left 
                            (trans (sym (idr E)) 
                                   (cong (comp E (right f)) 
                                         (trans (sym (fid L))
                                                (sym (idl E)))))))
               (trans (sym nat) 
                      (cong (comp D (HMap R (right f))) 
                            (trans (cong (comp D (left (iden E))) (fid J))
                                   (idr D))))) 
        (cong (comp D (HMap R (right f))) ηlaw)

alaw2lem : ∀{E}(T : Fun C D)(L : Fun C E)(R : Fun E D)
  (p : R ○ L ≅ T) → 
  (right : ∀ {X Y} → Hom D (OMap J X) (OMap R Y) → Hom E (OMap L X) Y) → 
  (bind : ∀{X Y} → 
          Hom D (OMap J X) (OMap T Y) → Hom D (OMap T X) (OMap T Y)) → 
  (natright : {X X' : Obj C} {Y Y' : Obj E} (f : Hom C X' X)
    (g : Hom E Y Y') (h : Hom D (OMap J X) (OMap R Y)) →
    right (comp D (HMap R g) (comp D h (HMap J f))) 
    ≅
    comp E g (comp E (right h) (HMap L f))) → 
  ∀{X}{Z}{W}
  {k : Hom D (OMap J Z) (OMap T W)}
  {f : Hom D (OMap J W) (OMap R X)} → 
  (bindlaw : HMap R (right (subst (Hom D (OMap J Z)) 
                           (fcong W (cong OMap (sym p))) 
                           k)) 
             ≅ 
             bind k) → 
  subst (λ Z → Hom D Z (OMap R X))
  (fcong Z (cong OMap p))
  (HMap R
   (right
    (comp D
     (subst (λ Z → Hom D Z (OMap R X))
      (fcong W (cong OMap p)) (HMap R (right f)))
     k)))
  ≅
  comp D
  (subst (λ Z → Hom D Z (OMap R X))
   (fcong W (cong OMap p)) (HMap R (right f)))
  (bind k)
alaw2lem {E} .(R ○ L) L R refl right bind natright {k = k}{f = f} bl = 
  trans (trans (cong (HMap R) 
                     (trans (cong (λ k → right (comp D (HMap R (right f)) k))
                                  (trans (sym (idr D)) (cong (comp D k) 
                                                             (sym (fid J)))))
                            (trans (trans (natright (iden C) (right f) k)
                                          (trans (sym (ass E))
                                                 (cong (comp E 
                                                             (comp E 
                                                                   (right f) 
                                                                   (right k)))
                                                       (fid L))))
                                   (idr E)))) 
               (fcomp R)) 
        (cong (comp D (HMap R (right f))) bl)

ahomlem : ∀{E}(T : Fun C D)(L : Fun C E)(R : Fun E D)
  (p : R ○ L ≅ T) → 
  (right : ∀ {X Y} → Hom D (OMap J X) (OMap R Y) → Hom E (OMap L X) Y) →
  (natright : {X X' : Obj C} {Y Y' : Obj E} (f : Hom C X' X)
    (g : Hom E Y Y') (h : Hom D (OMap J X) (OMap R Y)) →
    right (comp D (HMap R g) (comp D h (HMap J f))) 
    ≅
    comp E g (comp E (right h) (HMap L f))) → 
  {X : Obj E}{Y : Obj E}{f : Hom E X Y} →
  {Z : Obj C} {g : Hom D (OMap J Z) (OMap R X)} →
  comp D (HMap R f)
  (subst (λ Z → Hom D Z (OMap R X))
   (fcong Z (cong OMap p))
   (HMap R (right g))) 
  ≅
  subst (λ Z → Hom D Z (OMap R Y))
  (fcong Z (cong OMap p))
  (HMap R (right (comp D (HMap R f) g)))
ahomlem {E} .(R ○ L) L R refl right natright {X}{Y}{f}{Z}{g} = 
  trans (sym (fcomp R)) 
        (cong (HMap R) 
              (trans (trans (sym (idr E))
                            (trans (cong (comp E (comp E f (right g))) 
                                         (sym (fid L)))
                                   (trans (ass E) 
                                          (sym (natright (iden C) f g)))))
                     (cong (λ g → right (comp D (HMap R f) g)) 
                           (trans (cong (comp D g) (fid J)) (idr D)))))
open ObjAdj

Llawlem : ∀{E}(T : Fun C D)(L : Fun C E)(R : Fun E D)
  (p : R ○ L ≅ T) → 
  (right : ∀{X Y} → Hom D (OMap J X) (OMap R Y) → Hom E (OMap L X) Y) → 
  (bind : ∀{X Y} → 
          Hom D (OMap J X) (OMap T Y) → Hom D (OMap T X) (OMap T Y)) → 
  (bindlaw : {X Y : Obj C} {f : Hom D (OMap J X) (OMap T Y)} →
    HMap R
    (right
     (subst (Hom D (OMap J X)) (fcong Y (cong OMap (sym p))) f))
    ≅ bind f) → 
  ∀{X Z} → 
  {f  : Hom D (OMap J Z) (OMap R (OMap L X))}
  {f' : Hom D (OMap J Z) (OMap T X)} → (q  : f ≅ f') → 
  subst (λ Z → Hom D Z (OMap R (OMap L X)))
  (fcong Z (cong OMap p)) (HMap R (right f))
  ≅ bind f'
Llawlem .(R ○ L) L R refl right bind bindlaw {X}{Z}{f}{.f} refl = bindlaw

K : Fun (E A) (E EMObj)
K = record {
  OMap = λ X → record {
    acar = OMap (R (adj A)) X;
    astr = λ {Z} f →
      subst (λ Z₁ → Hom D Z₁ (OMap (R (adj A)) X))
            (fcong Z (cong OMap (law A))) 
            (HMap (R (adj A)) (right (adj A) f));
    alaw1 = λ {Z} {f} →
      alaw1lem 
               (TFun M) 
               (L (adj A)) 
               (R (adj A))
               (law A)
               η
               (right (adj A)) 
               (left (adj A)) 
               (ηlaw A)
               (natleft (adj A) (iden C) (right (adj A) f) (iden (E A)))
               (lawb (adj A) f);
    alaw2 = λ {Z} {W} {k} {f} →
      alaw2lem  
               (TFun M) 
               (L (adj A)) 
               (R (adj A))
               (law A)
               (right (adj A))
               bind
               (natright (adj A)) 
               (bindlaw A {_} {_} {k})};
  HMap = λ {X} {Y} f → record {
    amor = HMap (R (adj A)) f;
    ahom = λ {Z} {g} →
      ahomlem  
              (TFun M) 
              (L (adj A)) 
              (R (adj A)) 
              (law A) 
              (right (adj A))
              (natright (adj A)) };
    fid = RAlgMorphEq (fid (R (adj A)));
    fcomp = RAlgMorphEq (fcomp (R (adj A)))}

Llaw' : K ○ L (adj A) ≅ L (adj EMObj)
Llaw' = 
 FunctorEq _ _
   (ext
    (λ X →
       AlgEq (fcong X (cong OMap (law A)))
       (λ Z →
          dext
          (λ {f} {f'} p →
             Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
             bind (bindlaw A) p))))
   (λ {X} {Y} f →
      lemZ 
      (AlgEq (fcong X (cong OMap (law A)))
       (λ Z →
          dext
          (Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
           bind (bindlaw A))))
      (AlgEq (fcong Y (cong OMap (law A)))
       (λ Z →
          dext
          (Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
           bind (bindlaw A))))
      (cong' refl
       (ext
        (λ _ →
           cong₂ (Hom D) (fcong X (cong OMap (law A)))
           (fcong Y (cong OMap (law A)))))
       (icong' refl
        (ext
         (λ Z →
            cong₂ (λ x y → Hom C X Z → Hom D x y) (fcong X (cong OMap (law A)))
            (fcong Z (cong OMap (law A)))))
        (icong' refl
         (ext
          (λ Z →
             cong
             (λ (F : Obj C → Obj D) →
                {Y₁ : Obj C} → Hom C Z Y₁ → Hom D (F Z) (F Y₁))
             (cong OMap (law A))))
         (cong HMap (law A)) (refl {x = X}))
        (refl {x = Y}))
       (refl {x = f})))

Rlaw' : R (adj A) ≅ R (adj EMObj) ○ K
Rlaw' = FunctorEq _ _ refl (λ f → refl)

rightlaw' : {X : Obj C}{Y : Obj (E A)} →
            {f : Hom D (OMap J X) (OMap (R (adj A)) Y)} →
            HMap K (right (adj A) f) 
            ≅
            right (adj EMObj) {X} {OMap K Y}
                  (subst (Hom D (OMap J X)) (fcong Y (cong OMap Rlaw')) f)
rightlaw' {X}{Y}{f} = lemZ 
  (AlgEq (fcong X (cong OMap (law A)))
   (λ Z →
      dext
      (λ {g} {g'} p →
         Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
         bind (bindlaw A) p)))
  refl
  (trans
   (cong
    (λ (f₁ : Hom D (OMap J X) (OMap (R (adj A)) Y)) →
       HMap (R (adj A)) (right (adj A) f₁))
    (sym
       (stripsubst (Hom D (OMap J X)) f
        (fcong Y (cong OMap Rlaw')))))
   (sym
    (stripsubst (λ (Z : Obj D) → Hom D Z (OMap (R (adj A)) Y)) _
     (fcong X (cong OMap (law A))))))

EMHom : Hom CatofAdj A EMObj
EMHom = record { 
  K    = K; 
  Llaw = Llaw'; 
  Rlaw = Rlaw'; 
  rightlaw = rightlaw'}


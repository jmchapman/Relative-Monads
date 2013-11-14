{-# OPTIONS --type-in-type #-}

module TermRAdjHom where

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

open Cat
open Fun
open RAdj

alaw1lem : ∀{C D E}(J : Fun C D)(T : Fun C D)(L : Fun C E)(R : Fun E D)
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
alaw1lem {C}{D}{E} J .(R ○ L) L R refl η right left ηlaw {X}{Z}{f} nat lawb = 
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

alaw2lem : ∀{C D E}(J : Fun C D)(T : Fun C D)(L : Fun C E)(R : Fun E D)
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
alaw2lem {C}{D}{E} J .(R ○ L) L R refl right bind natright {k = k}{f = f} bl = 
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

ahomlem : ∀{C D E}(J : Fun C D)(T : Fun C D)(L : Fun C E)(R : Fun E D)
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
ahomlem {C}{D}{E} J .(R ○ L) L R refl right natright {X}{Y}{f}{Z}{g} = 
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

Llawlem : ∀{C D E}(J : Fun C D)(T : Fun C D)(L : Fun C E)(R : Fun E D)
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
Llawlem J .(R ○ L) L R refl right bind bindlaw {X}{Z}{f}{.f} refl = bindlaw

K : ∀{C D}{J : Fun C D}(M : RMonad J)(A : Obj (CatofAdj M)) → 
    Fun (E A) (E (EMObj M))
K {C}{D}{J} M A = record {
  OMap = λ X → record {
    acar = OMap (R (adj A)) X;
    astr = λ {Z} f →
      subst (λ Z₁ → Hom D Z₁ (OMap (R (adj A)) X))
            (fcong Z (cong OMap (law A))) 
            (HMap (R (adj A)) (right (adj A) f));
    alaw1 = λ {Z} {f} →
      alaw1lem J 
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
      alaw2lem J 
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
      ahomlem J 
              (TFun M) 
              (L (adj A)) 
              (R (adj A)) 
              (law A) 
              (right (adj A))
              (natright (adj A)) };
    fid = RAlgMorphEq M (fid (R (adj A)));
    fcomp = RAlgMorphEq M (fcomp (R (adj A)))}
  where open RMonad M

Llaw' : ∀{C D}{J : Fun C D}(M : RMonad J)(A : Obj (CatofAdj M)) → 
       K M A ○ L (adj A) ≅ L (adj (EMObj M))
Llaw' {C}{D}{J} M A = 
 FunctorEq _ _
   (ext
    (λ X →
       AlgEq M (fcong X (cong OMap (law A)))
       (λ Z →
          dext
          (λ {f} {f'} p →
             Llawlem J (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
             bind (bindlaw A) p))))
   (λ {X} {Y} f →
      lemZ {C} {D} {J} M
      (AlgEq M (fcong X (cong OMap (law A)))
       (λ Z →
          dext
          (Llawlem J (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
           bind (bindlaw A))))
      (AlgEq M (fcong Y (cong OMap (law A)))
       (λ Z →
          dext
          (Llawlem J (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
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
  where open RMonad M

Rlaw' : ∀{C D}{J : Fun C D}(M : RMonad J)(A : Obj (CatofAdj M)) → 
       R (adj A) ≅ R (adj (EMObj M)) ○ K M A
Rlaw' {C}{D}{J} M A = FunctorEq _ _ refl (λ f → refl)

rightlaw' : ∀{C D}{J : Fun C D}(M : RMonad J)(A : Obj (CatofAdj M)) → 
           {X : Obj C}{Y : Obj (E A)} →
           {f : Hom D (OMap J X) (OMap (R (adj A)) Y)} →
           HMap (K M A) (right (adj A) f) 
           ≅
           right (adj (EMObj M)) {X} {OMap (K M A) Y}
                 (subst (Hom D (OMap J X)) (fcong Y (cong OMap (Rlaw' M A))) f)
rightlaw' {C}{D}{J} M A {X}{Y}{f} = lemZ M
  (AlgEq M (fcong X (cong OMap (law A)))
   (λ Z →
      dext
      (λ {g} {g'} p →
         Llawlem J (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
         bind (bindlaw A) p)))
  refl
  (trans
   (cong
    (λ (f₁ : Hom D (OMap J X) (OMap (R (adj A)) Y)) →
       HMap (R (adj A)) (right (adj A) f₁))
    (sym
       (stripsubst (Hom D (OMap J X)) f
        (fcong Y (cong OMap (Rlaw' M A))))))
   (sym
    (stripsubst (λ (Z : Obj D) → Hom D Z (OMap (R (adj A)) Y)) _
     (fcong X (cong OMap (law A))))))
  where open RMonad M

EMHom : ∀{C D}{J : Fun C D}(M : RMonad J){A : Obj (CatofAdj M)} → 
        Hom (CatofAdj M) A (EMObj M)
EMHom {C}{D}{J} M {A} = record { 
  K    = K M A; 
  Llaw = Llaw' M A; 
  Rlaw = Rlaw' M A; 
  rightlaw = rightlaw' M A }


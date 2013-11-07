{-# OPTIONS --type-in-type #-}
module TermAdj2Hom where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Monads2
open import Categories
open import Functors
open import Adjunctions2
open import EM2
open import CatofAdj2
open import TermAdj2Obj


open Cat
open Fun
open Adj
open Monad

open ObjAdj

K' : ∀{C}(M : Monad C){A : Obj (CatofAdj M)} → Fun (D A) (D (EMObj M))
K' {C} M {A}  = record { 
    OMap  = λ X → record { 
      acar  = OMap (R (adj A)) X; 
      astr  = λ Z f → subst (λ Z → Hom C Z (OMap (R (adj A)) X)) 
                            (fcong Z (cong OMap (law A))) 
                            (HMap (R (adj A)) (right (adj A) f)); 
      alaw1 = λ {Z} {f} → alaw1lem 
         (TFun M) 
         (L (adj A))
         (R (adj A))
         (law A)
         (η M)
         (right (adj A)) 
         (left (adj A))
         (ηlaw A) 
         (natleft (adj A) (iden C) (right (adj A) f) (iden (D A)))
         (lawb (adj A) f);
      alaw2 = λ {Z} {W} {k} {f} → alaw2lem
         (TFun M) 
         (L (adj A))
         (R (adj A))
         (law A)
         (right (adj A))
         (bind M)
         (natright (adj A)) 
         (bindlaw A {_}{_}{k})}; 
    HMap  = λ {X} {Y} f → record { 
      amor = HMap (R (adj A)) f; 
      ahom = λ {Z} {g} → ahomlem 
         (TFun M) 
         (L (adj A))
         (R (adj A)) 
         (law A) 
         (right (adj A))
         (natright (adj A))}; 
    fid   = AlgMorphEq (fid (R (adj A))); 
    fcomp = AlgMorphEq (fcomp (R (adj A)))}

Llaw' : ∀{C}(M : Monad C){A : Obj (CatofAdj M)} → 
        K' M {A} ○ L (adj A) ≅ L (adj (EMObj M))
Llaw' {C} M {A} = FunctorEq _ _
                    (ext
                     (λ X →
                        AlgEq (fcong X (cong OMap (law A)))
                        (ext
                         (λ Z →
                            dext
                            (λ {f} {f'} p →
                               Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
                               (bind M) (bindlaw A) p)))))
                    (λ {X} {Y} f →
                       lemZ {C} {M}
                       (AlgEq (fcong X (cong OMap (law A)))
                        (ext
                         (λ Z →
                            dext
                            (λ {f₁} {f'} p →
                               Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
                               (bind M) (bindlaw A) p))))
                       (AlgEq (fcong Y (cong OMap (law A)))
                        (ext
                         (λ Z →
                            dext
                            (λ {f₁} {f'} p →
                               Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
                               (bind M) (bindlaw A) p))))
                          (dcong (refl {x = f}) (ext (λ _ → cong₂ (Hom C) (fcong X (cong OMap (law A)))
                                                              (fcong Y (cong OMap (law A)))))
                           (dicong (refl {x = Y}) (ext
                                                     (λ z →
                                                        cong (λ F → Hom C X z → Hom C (F X) (F z)) (cong OMap (law A))))
                            (dicong (refl {x = X}) (ext
                                                      (λ z →
                                                         cong (λ F → ∀ {y} → Hom C z y → Hom C (F z) (F y))
                                                         (cong OMap (law A)))) (cong HMap (law A))))))


Rlaw' : ∀{C}(M : Monad C){A : Obj (CatofAdj M)} → 
        R (adj A) ≅ R (adj (EMObj M)) ○ K' M {A}
Rlaw' {C} M {A}  = FunctorEq _ _ refl (λ f → refl)

rightlaw' : ∀{C}(M : Monad C){A : Obj (CatofAdj M)} → 
           {X : Obj C} {Y : Obj (D A)} {f : Hom C X (OMap (R (adj A)) Y)} →
           HMap (K' M {A}) (right (adj A) f) 
           ≅
           right (adj (EMObj M)) 
                 {X}
                 {OMap (K' M {A}) Y}
                 (subst (Hom C X) (fcong Y (cong OMap (Rlaw' M {A}))) f)
rightlaw' {C} M {A}{X}{Y}{f} = lemZ
                                 (AlgEq (fcong X (cong OMap (law A)))
                                  (ext
                                   (λ Z →
                                      dext
                                      (λ {g} {g'} p →
                                         Llawlem (TFun M) (L (adj A)) (R (adj A)) (law A) (right (adj A))
                                         (bind M) (bindlaw A) p))))
                                 refl
                                 (trans
                                  (cong
                                   (λ (f₁ : Hom C X (OMap (R (adj A)) Y)) →
                                      HMap (R (adj A)) (right (adj A) f₁))
                                   (sym
                                    (stripsubst (Hom C X) f
                                     (fcong Y
                                      (cong OMap
                                       (FunctorEq (R (adj A)) _ refl (λ {_} {_} f₁ → refl)))))))
                                  (sym
                                   (stripsubst (λ (Z : Obj C) → Hom C Z (OMap (R (adj A)) Y)) _
                                    (fcong X (cong OMap (law A))))))

EMHom : ∀{C}(M : Monad C){A : Obj (CatofAdj M)} → Hom (CatofAdj M) A (EMObj M) 
EMHom {C} M {A} = record { 
  K        = K' M {A}; 
  Llaw     = Llaw' M {A}; 
  Rlaw     = Rlaw' M {A}; 
  rightlaw = rightlaw' M {A} }

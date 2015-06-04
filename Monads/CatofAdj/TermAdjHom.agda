open import Categories
open import Monads
open import Level
import Monads.CatofAdj

module Monads.CatofAdj.TermAdjHom 
  {c d}
  {C : Cat {c}{d}}
  (M : Monad C)
  (A : Cat.Obj (Monads.CatofAdj.CatofAdj M {c ⊔ d}{c ⊔ d})) where

open import Library

open import Functors
open import Adjunctions
open import Monads.EM M
open Monads.CatofAdj M
open import Monads.CatofAdj.TermAdjObj M


open Cat
open Fun
open Adj
open Monad

open ObjAdj

K' : Fun (D A) (D EMObj)
K' = record { 
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

Llaw' : K' ○ L (adj A) ≅ L (adj EMObj)
Llaw' = FunctorEq 
  _ 
  _
  (ext (λ X → AlgEq 
    (fcong X (cong OMap (law A)))
    ((λ Z → dext (λ {f} {f'} p → Llawlem 
      (TFun M) 
      (L (adj A)) 
      (R (adj A)) 
      (law A) 
      (right (adj A))
      (bind M) 
      (bindlaw A) 
      p)))))
  (λ {X} {Y} f → AlgMorphEq' 
    (AlgEq 
      (fcong X (cong OMap (law A)))
      ((λ Z → dext (λ {f₁} {f'} p → Llawlem 
        (TFun M) 
        (L (adj A))
        (R (adj A)) 
        (law A) 
        (right (adj A))
        (bind M) 
        (bindlaw A) 
        p))))
    (AlgEq 
      (fcong Y (cong OMap (law A)))
      ((λ Z → dext (λ {f₁} {f'} p → Llawlem 
        (TFun M) 
        (L (adj A)) 
        (R (adj A)) 
        (law A) 
        (right (adj A))
        (bind M) 
        (bindlaw A) 
        p))))
    (dcong 
      (refl {x = f}) 
      (ext (λ _ → cong₂ 
        (Hom C) 
        (fcong X (cong OMap (law A)))
        (fcong Y (cong OMap (law A)))))
      (dicong 
        (refl {x = Y}) 
        (ext (λ z → cong 
          (λ F → Hom C X z → Hom C (F X) (F z)) 
          (cong OMap (law A))))
        (dicong 
          (refl {x = X}) 
          (ext (λ z → cong 
            (λ F → ∀ {y} → Hom C z y → Hom C (F z) (F y))
            (cong OMap (law A)))) 
          (cong HMap (law A))))))

Rlaw' : R (adj A) ≅ R (adj EMObj) ○ K'
Rlaw' = FunctorEq _ _ refl (λ f → refl)

rightlaw' : {X : Obj C} {Y : Obj (D A)} {f : Hom C X (OMap (R (adj A)) Y)} →
            HMap K' (right (adj A) f) 
            ≅
            right (adj EMObj) 
                  {X}
                  {OMap K' Y}
                  (subst (Hom C X) (fcong Y (cong OMap Rlaw')) f)
rightlaw' {X = X}{Y = Y}{f = f} = AlgMorphEq'
  (AlgEq (fcong X (cong OMap (law A)))
         (λ Z → dext (λ p → Llawlem (TFun M) 
           (L (adj A)) 
           (R (adj A)) 
           (law A) 
           (right (adj A))
           (bind M) 
           (bindlaw A) p )))
  refl
  (trans (cong  (λ (f₁ : Hom C X (OMap (R (adj A)) Y)) →
           HMap (R (adj A)) (right (adj A) f₁)) (sym (stripsubst (Hom C X) f (fcong Y (cong OMap Rlaw')))) ) (sym (stripsubst (λ Z → Hom C Z (OMap (R (adj A)) Y)) ( ((HMap (R (adj A))
 (right (adj A)
   (subst (Hom C X) (fcong Y (cong (λ r → OMap r) Rlaw')) f))))) (fcong X (cong OMap (law A))))))

EMHom : Hom CatofAdj A EMObj
EMHom = record { 
  K        = K';
  Llaw     = Llaw'; 
  Rlaw     = Rlaw'; 
  rightlaw = rightlaw'}


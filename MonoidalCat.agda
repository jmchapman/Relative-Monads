module MonoidalCat where

open import Library hiding (_×_)
open import Categories
open import Categories.Products
open import Functors
open import Naturals

record Monoidal {l}{m} : Set (lsuc (l ⊔ m)) where
  field C : Cat {l}{m}
  open Cat C
  open Fun
  open NatI
  field ⊗ : Fun (C × C) C
        I : Obj
        
  I⊗- : Fun C C
  I⊗- = functor
    (\ A -> OMap ⊗ (I , A))
    (\ f -> HMap ⊗ (iden , f))
    (fid ⊗)
    (trans (cong (\f -> HMap ⊗ (f , _)) (sym idl)) (fcomp ⊗))

  field λ'  : NatI I⊗- (IdF C)

  -⊗I : Fun C C
  -⊗I = functor
    (\ A -> OMap ⊗ (A , I))
    (\ f -> HMap ⊗ (f , iden))
    (fid ⊗)
    (trans (cong (\f -> HMap ⊗ (_ , f)) (sym idl)) (fcomp ⊗))

  field ρ  : NatI -⊗I (IdF C)

  [-⊗-]⊗- : Fun (C × C × C) C
  [-⊗-]⊗- = functor
    (λ {(X , Y , Z) → OMap ⊗ (OMap ⊗ (X , Y) , Z)})
    (λ {(f , g , h) → HMap ⊗ (HMap ⊗ (f , g) , h)})
    (trans (cong (\f -> HMap ⊗ (f , _)) (fid ⊗) ) (fid ⊗))
    (trans (cong (\f -> HMap ⊗ (f , _)) (fcomp ⊗)) (fcomp ⊗))

  -⊗[-⊗-] : Fun (C × C × C) C
  -⊗[-⊗-] = functor
    (λ {(X , Y , Z) → OMap ⊗ (X , OMap ⊗ (Y , Z))})
    (λ {(f , g , h) → HMap ⊗ (f , HMap ⊗ (g , h))})
    (trans (cong (\f -> HMap ⊗ (_ , f)) (fid ⊗) ) (fid ⊗))
    (trans (cong (\f -> HMap ⊗ (_ , f)) (fcomp ⊗)) (fcomp ⊗))

  field α : NatI [-⊗-]⊗- -⊗[-⊗-]

        triangle : ∀{A B} ->
          comp (HMap ⊗ (iden {A} , (cmp λ' {B}))) (cmp α {A , I , B})
          ≅  HMap ⊗ (cmp ρ {A} , iden {B}) 

        square : ∀{A B C D} ->
          comp (HMap ⊗ (iden {A} , cmp α {B , C , D}))
               (comp (cmp α {A , OMap ⊗ (B , C) , D})
                     (HMap ⊗ (cmp α {A , B , C} , iden {D})))
          ≅
          comp (cmp α {A , B , OMap ⊗ (C , D)})
               (cmp α {OMap ⊗ (A , B) , C , D}) 

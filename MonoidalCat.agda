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

record MonoidalFun {a b c d}(M : Monoidal {a}{b})(M' : Monoidal {c}{d})
  : Set (a ⊔ b ⊔ c ⊔ d) where
  open Monoidal
  open Cat

  field F : Fun (C M) (C M')

  open Fun

  field e : Hom (C M') (I M') (OMap F (I M))

  F-⊗'F- : Fun (C M × C M) (C M')
  F-⊗'F- = functor
    (\ {(A , B) -> OMap (⊗ M') (OMap F A , OMap F B)})
    (\ {(f , g) -> HMap (⊗ M') (HMap F f , HMap F g)})
    (trans (cong₂ (\f g -> HMap (⊗ M') (f , g)) (fid F) (fid F)) (fid (⊗ M')))
    (trans (cong₂ (\f g -> HMap (⊗ M') (f , g))
           (fcomp F) (fcomp F)) (fcomp (⊗ M')))

  F[-⊗-] : Fun (C M × C M) (C M')
  F[-⊗-] = functor
    (λ { (A , B) → OMap F (OMap (⊗ M) (A , B)) })
    ((λ { (f , g) → HMap F (HMap (⊗ M) (f , g)) }))
    (trans (cong (HMap F) (fid (⊗ M))) (fid F))
    (trans (cong (HMap F) (fcomp (⊗ M))) (fcomp F))


  field m : NatT F-⊗'F- F[-⊗-]
  
  field square1 : ∀{A} ->
          NatI.cmp (ρ M') {OMap F A}
          ≅
          comp (C M') (HMap F (NatI.cmp (ρ M) {A}))
                      (comp (C M') (NatT.cmp m {A , I M})
                                   (HMap (⊗ M') (iden (C M') {OMap F A} , e)))

        square2 : ∀{B} ->
          NatI.cmp (λ' M') {OMap F B}
          ≅
          comp (C M') (HMap F (NatI.cmp (λ' M) {B}))
                      (comp (C M') (NatT.cmp m {I M , B})
                                   (HMap (⊗ M') (e , iden (C M') {OMap F B})))


        hexagon : ∀{A B B'} ->
           comp (C M') (HMap F (NatI.cmp (α M) {A , B , B'}))
                       (comp (C M') (NatT.cmp m {OMap (⊗ M) (A , B) , B'})
                                    (HMap (⊗ M') (NatT.cmp m {A , B} ,
                                                  iden (C M') {OMap F B'})))
           ≅
           comp (C M') (NatT.cmp m {A , OMap (⊗ M) (B , B')})
                       (comp (C M') (HMap (⊗ M') (iden (C M') {OMap F A} ,
                                                  NatT.cmp m {B , B'}))
                                    (NatI.cmp (α M') {OMap F A ,
                                                      OMap F B ,
                                                      OMap F B'}))

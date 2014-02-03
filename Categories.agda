
module Categories where

open import Library

record Cat {a b} : Set (lsuc (a ⊔ b)) where
  field Obj  : Set a
        Hom  : Obj → Obj → Set b
        iden : ∀{X} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp (comp f g) h ≅ comp f (comp g h)
open Cat

{-
!_! : Cat → Set
! C !  = Obj C

_<_,_> : (C : Cat) → Obj C → Obj C → Set
C < X , Y > = Hom C X Y

_!_•_ : ∀ C {X Y Z : ! C !} → C < Y , Z > → C < X , Y > → C < X , Z >
C ! f • g = comp C f g
-}

_Op : ∀{a b} →  Cat {a}{b} → Cat
C Op = record{
  Obj  = Obj C; 
  Hom  = λ X Y → Hom C Y X;
  iden = iden C;
  comp = λ f g → comp C g f; 
  idl  = idr C;
  idr  = idl C;
  ass  = sym (ass C)}

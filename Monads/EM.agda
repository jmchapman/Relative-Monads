open import Categories
open import Monads

module Monads.EM {a b}{C : Cat {a}{b}}(M : Monad C) where

open import Library

open import Functors
open Cat C
open Monad M

record Alg : Set (a ⊔ b) where
  constructor alg
  field acar  : Obj
        astr  : ∀ Z → Hom Z acar → Hom (T Z) acar
        alaw1 : ∀ {Z}{f : Hom Z acar} → f ≅ comp (astr Z f) η
        alaw2 : ∀{Z}{W}{k : Hom Z (T W)}{f : Hom W acar} → 
                astr Z (comp (astr W f) k) ≅ comp (astr W f) (bind k)
open Alg

AlgEq : {X Y : Alg} → acar X ≅ acar Y → (astr X ≅ astr Y) → X ≅ Y
AlgEq {alg acar astr _ _} {alg ._ ._ _ _} refl refl =
  cong₂ (alg acar astr)
        (iext λ _ → iext λ _ → ir _ _)
        (iext λ _ → iext λ _ → iext λ _ → iext λ _ → ir _ _)

record AlgMorph (A B : Alg) : Set (a ⊔ b) where
  constructor algmorph
  field amor : Hom (acar A) (acar B)
        ahom : ∀{Z}{f : Hom Z (acar A)} → 
               comp amor (astr A Z f) ≅ astr B Z (comp amor f)
open AlgMorph

AlgMorphEq : {X Y : Alg}{f g : AlgMorph X Y} → amor f ≅ amor g → f ≅ g
AlgMorphEq {f = algmorph amor _}{algmorph .amor _} refl =
  cong (algmorph amor)
       (iext λ _ → iext λ _ → ir _ _)

AlgMorphEq' : {X X' Y Y' : Alg}
  {f : AlgMorph X Y}{g : AlgMorph X' Y'} → X ≅ X' → Y ≅ Y' → 
  amor f ≅ amor g → f ≅ g
AlgMorphEq' refl refl = AlgMorphEq

IdMorph : {A : Alg} → AlgMorph A A
IdMorph {A} = record {
  amor = iden;
  ahom = λ {Z} {f} → 
    proof 
    comp iden (astr A Z f) 
    ≅⟨ idl ⟩ 
    astr A Z f
    ≅⟨ cong (astr A Z) (sym idl) ⟩ 
    astr A Z (comp iden f) 
    ∎}

CompMorph : {X Y Z : Alg} → AlgMorph Y Z → AlgMorph X Y → AlgMorph X Z
CompMorph {X}{Y}{Z} f g = record {
  amor = comp (amor f) (amor g);
  ahom = λ{W}{h} → 
    proof
    comp (comp (amor f) (amor g)) (astr X W h) 
    ≅⟨ ass ⟩
    comp (amor f) (comp (amor g) (astr X W h))
    ≅⟨ cong (comp (amor f)) (ahom g) ⟩
    comp (amor f) (astr Y W (comp (amor g) h))
    ≅⟨ ahom f ⟩
    astr Z W (comp (amor f) (comp (amor g) h)) 
    ≅⟨ cong (astr Z W) (sym ass) ⟩
    astr Z W (comp (comp (amor f) (amor g)) h) 
    ∎}

idlMorph : {X Y : Alg}{f : AlgMorph X Y} → CompMorph IdMorph f ≅ f
idlMorph = AlgMorphEq idl

idrMorph : {X Y : Alg}{f : AlgMorph X Y} → CompMorph f IdMorph ≅ f
idrMorph = AlgMorphEq idr
  
assMorph : {W X Y Z : Alg}
           {f : AlgMorph Y Z}{g : AlgMorph X Y}{h : AlgMorph W X} →
           CompMorph (CompMorph f g) h ≅ CompMorph f (CompMorph g h)
assMorph = AlgMorphEq ass

EM : Cat {a ⊔ b}{a ⊔ b}
EM  = record{
  Obj  = Alg;
  Hom  = AlgMorph;
  iden = IdMorph;
  comp = CompMorph;
  idl  = idlMorph;
  idr  = idrMorph;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → assMorph {W}{X}{Y}{Z}{f}{g}{h}}
-- -}

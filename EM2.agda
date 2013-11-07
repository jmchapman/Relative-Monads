{-# OPTIONS --type-in-type #-}
module EM2 where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Categories
open import Functors
open import Monads2

open Cat
open Monad

record Alg {C : Cat}(M : Monad C) : Set where
  field acar  : Obj C
        astr  : ∀ Z → Hom C Z acar → Hom C (T M Z) acar
        alaw1 : ∀ {Z}{f : Hom C Z acar} → f ≅ comp C (astr Z f) (η M)
        alaw2 : ∀{Z}{W}{k : Hom C Z (T M W)}{f : Hom C W acar} → 
                astr Z (comp C (astr W f) k) ≅ comp C (astr W f) (bind M k)
open Alg

AlgEq : ∀{C}{M : Monad C}{X Y : Alg M} → acar X ≅ acar Y → astr X ≅ astr Y → 
        X ≅ Y
AlgEq {C}{M}{X}{Y} p q = funnycong4 {Obj C}
  {λ acar₁ → (Z : _) → Hom C Z acar₁ → Hom C (T M Z) acar₁}
  {λ acar₁ astr₁ → {Z : _} {f : Hom C Z acar₁} → f ≅ comp C (astr₁ Z f) (η M)}
  {λ acar₁ astr₁ _ → {Z W : _} {k : Hom C Z (T M W)} {f : Hom C W acar₁} →
     astr₁ Z (comp C (astr₁ W f) k) ≅ comp C (astr₁ W f) (bind M k)}
  {Alg {C} M}
  (λ x y z z' → record { acar = x; astr = y; alaw1 = z; alaw2 = z' })
  p 
  q
  (iext (λ Z → diext (λ {f f'} r → fixtypes (trans (sym (alaw1 X)) r))))
  (iext (λ Z → iext (λ Z' → iext (λ f → diext (λ {g} {g'} r → 
    fixtypes (trans (cong₂ (λ Ran h → comp C {T M Z} {T M Z'} {Ran} h (bind M f)) p (dcong r 
            (dext (λ _ → cong (Hom C (T M Z')) p)) 
            (dcong (refl {x = Z'}) 
                   (dext (λ p' → cong₂ (λ f g → Hom C f g → Hom C (T M f) g) 
                                       p' 
                                       p)) 
                   q))) 
                     (sym (alaw2 Y))))))))


record AlgMorph {C : Cat}{M : Monad C}(A B : Alg M) : Set where
  field amor : Hom C (acar A) (acar B)
        ahom : ∀{Z}{f : Hom C Z (acar A)} → 
               comp C amor (astr A Z f) ≅ astr B Z (comp C amor f)
open AlgMorph

AlgMorphEq : ∀{C}{M : Monad C}{X Y : Alg M}{f g : AlgMorph X Y} → 
             amor f ≅ amor g → f ≅ g
AlgMorphEq {C}{M}{X}{Y}{f}{g} p = funnycong
  {Hom C (acar X) (acar Y)}
  {λ amor → ∀{Z}{f : Hom C Z (acar X)} → 
    comp C amor (astr X Z f) ≅ astr Y Z (comp C amor f)}
  p
  (iext λ Z → iext λ h → fixtypes 
    (trans (sym (ahom f)) 
           (cong (λ f₁ → comp C f₁ (astr X Z h)) p)))
  λ x y → record{amor = x;ahom = y} 

lemZ : ∀{C}{M : Monad C}{X X' Y Y' : Alg M}
       {f : AlgMorph X Y}{g : AlgMorph X' Y'} → X ≅ X' → Y ≅ Y' → 
             amor f ≅ amor g → f ≅ g
lemZ refl refl = AlgMorphEq

IdMorph : ∀{C}{M : Monad C}{A : Alg M} → AlgMorph A A
IdMorph {C}{M}{A} = record {
  amor = iden C;
  ahom = trans (idl C) (cong (astr A _) (sym (idl C)))}

CompMorph : ∀{C}{M : Monad C}{X Y Z : Alg M} → 
            AlgMorph Y Z → AlgMorph X Y → AlgMorph X Z
CompMorph {C}{M}{X}{Y}{Z} f g = record {
  amor = comp C (amor f) (amor g);
  ahom = λ{W}{h} → 
    trans (trans (trans (ass C) 
                        (cong (comp C (amor f)) (ahom g))) 
                 (ahom f)) 
          (cong (astr Z W) (sym (ass C)))}

idlMorph : ∀{C}{M : Monad C}{X Y : Alg M}{f : AlgMorph X Y} → 
           CompMorph IdMorph f ≅ f
idlMorph {C} = AlgMorphEq (idl C)

idrMorph : ∀{C}{M : Monad C}{X Y : Alg M}{f : AlgMorph X Y} → 
           CompMorph f IdMorph ≅ f
idrMorph {C} = AlgMorphEq (idr C) 
  
assMorph : ∀{C}{M : Monad C}{W X Y Z : Alg M}
           {f : AlgMorph Y Z}{g : AlgMorph X Y}{h : AlgMorph W X} →
           CompMorph (CompMorph f g) h ≅ CompMorph f (CompMorph g h)
assMorph {C} = AlgMorphEq (ass C)

EM : ∀{C} → Monad C → Cat
EM {C} M = record{
  Obj  = Alg M;
  Hom  = AlgMorph;
  iden = IdMorph;
  comp = CompMorph;
  idl  = idlMorph;
  idr  = idrMorph;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → assMorph {C}{M}{W}{X}{Y}{Z}{f}{g}{h}}

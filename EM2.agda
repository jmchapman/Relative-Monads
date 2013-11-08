{-# OPTIONS --type-in-type #-}
module EM2 where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Equality
open import Categories
open import Functors
open import Monads2


record Alg {C : Cat}(M : Monad C) : Set where
  open Cat
  open Monad
  field acar  : Obj C
        astr  : ∀ Z → Hom C Z acar → Hom C (T M Z) acar
        alaw1 : ∀ {Z}{f : Hom C Z acar} → f ≅ comp C (astr Z f) (η M)
        alaw2 : ∀{Z}{W}{k : Hom C Z (T M W)}{f : Hom C W acar} → 
                astr Z (comp C (astr W f) k) ≅ comp C (astr W f) (bind M k)
open Alg

AlgEq : ∀{C}{M : Monad C}{X Y : Alg M} → acar X ≅ acar Y → astr X ≅ astr Y → 
        X ≅ Y
AlgEq {C}{M}{X}{Y} p q = let open Cat C; open Monad M in funnycong4 
  {Obj}
  {λ acar → ∀ Z → Hom Z acar → Hom (T Z) acar}
  {λ acar astr → ∀{Z}{f : Hom Z acar} → f ≅ comp (astr Z f) η}
  {λ acar astr _ → ∀{Z W}{k : Hom Z (T W)} {f : Hom W acar} →
     astr Z (comp (astr W f) k) ≅ comp (astr W f) (bind k)}
  (λ x y z z' → record { acar = x; astr = y; alaw1 = z; alaw2 = z' })
  p 
  q
  (iext λ Z → diext λ {f f'} r → fixtypes (
    proof 
    comp (astr X Z f) η 
    ≅⟨ sym (alaw1 X) ⟩ 
    f 
    ≅⟨ r ⟩ 
    f' 
    ∎))
  (iext λ Z → iext λ Z' → iext λ f → diext λ {g} {g'} r → 
    fixtypes (
      proof
      comp (astr X Z' g) (bind f) 
      ≅⟨ cong₂ (λ X₁ h → comp {T Z} {T Z'} {X₁} h (bind f)) 
               p 
               (dcong r 
                      (dext (λ _ → cong (Hom (T Z')) p)) 
                      (dcong (refl {x = Z'}) 
                             (dext λ p' → cong₂ (λ f g → Hom f g → Hom (T f) g)
                                                p' 
                                                p)
                             q)) ⟩
      comp (astr Y Z' g') (bind f)
      ≅⟨ sym (alaw2 Y) ⟩
      astr Y Z (comp (astr Y Z' g') f) 
      ∎))


record AlgMorph {C : Cat}{M : Monad C}(A B : Alg M) : Set where
  open Cat C
  field amor : Hom (acar A) (acar B)
        ahom : ∀{Z}{f : Hom Z (acar A)} → 
               comp amor (astr A Z f) ≅ astr B Z (comp amor f)
open AlgMorph

AlgMorphEq : ∀{C}{M : Monad C}{X Y : Alg M}{f g : AlgMorph X Y} → 
             amor f ≅ amor g → f ≅ g
AlgMorphEq {C}{M}{X}{Y}{f}{g} p = let open Cat C in funnycong
  {Hom (acar X) (acar Y)}
  {λ amor → ∀{Z}{f : Hom Z (acar X)} → 
    comp amor (astr X Z f) ≅ astr Y Z (comp amor f)}
  p
  (iext λ Z → iext λ h → fixtypes (
    proof
    astr Y Z (comp (amor f) h) 
    ≅⟨ sym (ahom f) ⟩ 
    comp (amor f) (astr X Z h) 
    ≅⟨ cong (λ f → comp f (astr X Z h)) p ⟩ 
    comp (amor g) (astr X Z h) 
    ∎))
  λ x y → record{amor = x;ahom = y} 

AlgMorphEq' : ∀{C}{M : Monad C}{X X' Y Y' : Alg M}
       {f : AlgMorph X Y}{g : AlgMorph X' Y'} → X ≅ X' → Y ≅ Y' → 
             amor f ≅ amor g → f ≅ g
AlgMorphEq' refl refl = AlgMorphEq

IdMorph : ∀{C}{M : Monad C}{A : Alg M} → AlgMorph A A
IdMorph {C}{M}{A} = let open Cat C in record {
  amor = iden;
  ahom = trans idl (cong (astr A _) (sym idl))}

CompMorph : ∀{C}{M : Monad C}{X Y Z : Alg M} → 
            AlgMorph Y Z → AlgMorph X Y → AlgMorph X Z
CompMorph {C}{M}{X}{Y}{Z} f g = let open Cat C in record {
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

idlMorph : ∀{C}{M : Monad C}{X Y : Alg M}{f : AlgMorph X Y} → 
           CompMorph IdMorph f ≅ f
idlMorph {C} = AlgMorphEq (Cat.idl C)

idrMorph : ∀{C}{M : Monad C}{X Y : Alg M}{f : AlgMorph X Y} → 
           CompMorph f IdMorph ≅ f
idrMorph {C} = AlgMorphEq (Cat.idr C) 
  
assMorph : ∀{C}{M : Monad C}{W X Y Z : Alg M}
           {f : AlgMorph Y Z}{g : AlgMorph X Y}{h : AlgMorph W X} →
           CompMorph (CompMorph f g) h ≅ CompMorph f (CompMorph g h)
assMorph {C} = AlgMorphEq (Cat.ass C)

EM : ∀{C} → Monad C → Cat
EM {C} M = record{
  Obj  = Alg M;
  Hom  = AlgMorph;
  iden = IdMorph;
  comp = CompMorph;
  idl  = idlMorph;
  idr  = idrMorph;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → assMorph {C}{M}{W}{X}{Y}{Z}{f}{g}{h}}

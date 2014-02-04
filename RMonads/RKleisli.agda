{-# OPTIONS --type-in-type #-}
open import Functors
open import RMonads

module RMonads.RKleisli {C D}{J : Fun C D}(M : RMonad J) where

open import Library
open import Categories

open Cat
open Fun
open RMonad M

Kl : Cat
Kl = record{
  Obj  = Obj C; 
  Hom  = λ X Y → Hom D (OMap J X) (T Y);
  iden = η;
  comp = λ f g → comp D (bind f) g;
  idl  = λ{X}{Y}{f} → 
    proof 
    comp D (bind η) f 
    ≅⟨ cong (λ g → comp D g f) law1 ⟩ 
    comp D (iden D) f 
    ≅⟨ idl D ⟩ 
    f 
    ∎; 
  idr  = law2;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → 
    proof
    comp D (bind (comp D (bind f) g)) h 
    ≅⟨ cong (λ f₁ → comp D f₁ h) law3 ⟩
    comp D (comp D (bind f) (bind g)) h
    ≅⟨ ass D ⟩
    comp D (bind f) (comp D (bind g) h) 
    ∎}

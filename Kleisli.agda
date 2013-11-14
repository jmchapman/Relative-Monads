{-# OPTIONS --type-in-type #-}
module Kleisli where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories
open import Monads

Kl : ∀{C} → Monad C → Cat
Kl {C} M = let open Cat C; open Monad M in record{
  Obj  = Obj;
  Hom  = λ X Y → Hom X (T Y);
  iden = η;
  comp = λ f g → comp (bind f) g;
  idl  = λ{X}{Y}{f} → 
    proof
    comp (bind η) f 
    ≅⟨ cong (λ g → comp g f) law1 ⟩ 
    comp iden f 
    ≅⟨ idl ⟩ 
    f 
    ∎;
  idr  = law2;
  ass  = λ{W}{X}{Y}{Z}{f}{g}{h} → 
    proof
    comp (bind (comp (bind f) g)) h 
    ≅⟨ cong (λ f → comp f h) law3 ⟩
    comp (comp (bind f) (bind g)) h
    ≅⟨ ass ⟩
    comp (bind f) (comp (bind g) h) 
    ∎}


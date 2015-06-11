open import Categories
open import Monads

module Monads.Kleisli {a b}{C : Cat {a}{b}}(M : Monad C) where

open import Library
open Cat C
open Monad M

Kl : Cat
Kl = record{
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
  ass  = λ{_}{_}{_}{_}{f}{g}{h} → 
    proof
    comp (bind (comp (bind f) g)) h 
    ≅⟨ cong (λ f → comp f h) law3 ⟩
    comp (comp (bind f) (bind g)) h
    ≅⟨ ass ⟩
    comp (bind f) (comp (bind g) h) 
    ∎}

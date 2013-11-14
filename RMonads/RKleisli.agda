{-# OPTIONS --type-in-type #-}
module RMonads.RKleisli where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories
open import Functors
open import RMonads

open Cat
open Fun

Kl : ∀{C D}{J : Fun C D}  → RMonad J → Cat
Kl {C}{D}{J} M = let open RMonad M in record{
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
  ass  =  λ{W}{X}{Y}{Z}{f}{g}{h} → 
    proof
    comp D (bind (comp D (bind f) g)) h 
    ≅⟨ cong (λ f₁ → comp D f₁ h) law3 ⟩
    comp D (comp D (bind f) (bind g)) h
    ≅⟨ ass D ⟩
    comp D (bind f) (comp D (bind g) h) 
    ∎}

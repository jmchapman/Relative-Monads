open import Categories
open import Functors
import RMonads

module RMonads.RKleisli 
  {a b c d}
  {C : Cat {a}{b}}
  {D : Cat {c}{d}}
  {J : Fun C D} 
  (M : RMonads.RMonad J) where

open import Library
open RMonads.RMonad M
open Cat
open Fun

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
  ass  =  λ{_ _ _ _ f g h} → 
    proof
    comp D (bind (comp D (bind f) g)) h 
    ≅⟨ cong (λ f → comp D f h) law3 ⟩
    comp D (comp D (bind f) (bind g)) h
    ≅⟨ ass D ⟩
    comp D (bind f) (comp D (bind g) h) 
    ∎}

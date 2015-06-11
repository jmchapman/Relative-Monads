module Adjunctions.Adj2Mon where

open import Library
open import Categories
open import Functors
open import Monads
open import Adjunctions

open Cat
open Fun

Adj2Mon : ∀{a b}{C D : Cat {a}{b}} → Adj C D → Monad C
Adj2Mon {C = C}{D} A = record{
  T    = OMap R ∘ OMap L;
  η    = left (iden D);
  bind = HMap R ∘ right;
  law1 =
    proof
    HMap R (right (left (iden D)))
    ≅⟨ cong (HMap R) (lawa (iden D)) ⟩
    HMap R (iden D)
    ≅⟨ fid R ⟩
    iden C ∎; 
  law2 = λ{_}{_}{f} → 
    proof
    comp C (HMap R (right f)) (left (iden D)) 
    ≅⟨ cong (comp C (HMap R (right f))) (sym (idr C)) ⟩
    comp C (HMap R (right f)) (comp C (left (iden D)) (iden C))
    ≅⟨ natleft (iden C) (right f) (iden D) ⟩
    left (comp D (right f) (comp D (iden D) (HMap L (iden C))))
    ≅⟨ cong (left ∘ comp D (right f)) (idl D) ⟩
    left (comp D (right f) (HMap L (iden C)))
    ≅⟨ cong (left ∘ comp D (right f)) (fid L) ⟩
    left (comp D (right f) (iden D))
    ≅⟨ cong (left) (idr D) ⟩
    left (right f)
    ≅⟨ lawb f ⟩
    f ∎; 
  law3 = λ{_}{_}{_}{f}{g} → 
    proof
    HMap R (right (comp C (HMap R (right g)) f))
    ≅⟨ cong (HMap R ∘ right ∘ comp C (HMap R (right g))) 
            (sym (idr C)) ⟩
    HMap R (right (comp C (HMap R (right g)) (comp C f (iden C))))
    ≅⟨ cong (HMap R) (natright (iden C) (right g) f) ⟩
    HMap R (comp D (right g) (comp D (right f) (HMap L (iden C))))
    ≅⟨ cong (HMap R ∘ comp D (right g) ∘ comp D (right f)) (fid L)⟩
    HMap R (comp D (right g) (comp D (right f) (iden D)))
    ≅⟨ cong (HMap R ∘ comp D (right g)) (idr D) ⟩
    HMap R (comp D (right g) (right f))
    ≅⟨ fcomp R ⟩
    comp C (HMap R (right g)) (HMap R (right f))
    ∎} 
  where open Adj A

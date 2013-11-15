{-# OPTIONS --type-in-type #-}
module Adjunctions.Adj2Mon where

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories
open import Functors
open import Monads
open import Adjunctions

open Cat
open Fun
open Adj

Adj2Mon : ∀{C D} → Adj C D → Monad C
Adj2Mon {C}{D} A = record{
  T    = OMap (R A) ∘ OMap (L A);
  η    = left A (iden D);
  bind = HMap (R A) ∘ right A;
  law1 =
    proof
    HMap (R A) (right A (left A (iden D)))
    ≅⟨ cong (HMap (R A)) (lawa A (iden D)) ⟩
    HMap (R A) (iden D)
    ≅⟨ fid (R A) ⟩
    iden C ∎; 
  law2 = λ{X}{Y}{f} → 
    proof
    comp C (HMap (R A) (right A f)) (left A (iden D)) 
    ≅⟨ cong (comp C (HMap (R A) (right A f))) (sym (idr C)) ⟩
    comp C (HMap (R A) (right A f)) (comp C (left A (iden D)) (iden C))
    ≅⟨ natleft A (iden C) (right A f) (iden D) ⟩
    left A (comp D (right A f) (comp D (iden D) (HMap (L A) (iden C))))
    ≅⟨ cong (left A ∘ comp D (right A f)) (idl D) ⟩
    left A (comp D (right A f) (HMap (L A) (iden C)))
    ≅⟨ cong (left A ∘ comp D (right A f)) (fid (L A)) ⟩
    left A (comp D (right A f) (iden D))
    ≅⟨ cong (left A) (idr D) ⟩
    left A (right A f)
    ≅⟨ lawb A f ⟩
    f ∎; 
  law3 = λ{X}{Y}{Z}{f}{g} → 
    proof
    HMap (R A) (right A (comp C (HMap (R A) (right A g)) f))
    ≅⟨ cong (HMap (R A) ∘ right A ∘ comp C (HMap (R A) (right A g))) 
            (sym (idr C)) ⟩
    HMap (R A) (right A (comp C (HMap (R A) (right A g)) (comp C f (iden C))))
    ≅⟨ cong (HMap (R A)) (natright A (iden C) (right A g) f) ⟩
    HMap (R A) (comp D (right A g) (comp D (right A f) (HMap (L A) (iden C))))
    ≅⟨ cong (HMap (R A) ∘ comp D (right A g) ∘ comp D (right A f)) (fid (L A))⟩
    HMap (R A) (comp D (right A g) (comp D (right A f) (iden D)))
    ≅⟨ cong (HMap (R A) ∘ comp D (right A g)) (idr D) ⟩
    HMap (R A) (comp D (right A g) (right A f))
    ≅⟨ fcomp (R A) ⟩
    comp C (HMap (R A) (right A g)) (HMap (R A) (right A f))
    ∎} 

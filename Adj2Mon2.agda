{-# OPTIONS --type-in-type #-}
module Adj2Mon2 where

open import Function
open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Monads2
open import Adjunctions2

open Cat
open Fun
open Adj

Adj2Mon : ∀{C D} → Adj C D → Monad C
Adj2Mon {C}{D} A = record{
  T    = OMap (R A) ∘ OMap (L A);
  η    = left A (iden D);
  bind = λ f → HMap (R A) (right A f);
  law1 = trans (cong (HMap (R A)) (lawa A (iden D))) (fid (R A));
  law2 = λ{X}{Y}{f} → trans (sym (idr C)) (trans (ass C) (trans (natleft A (iden C) (right A f) (iden D)) (trans (cong (left A) (trans (sym (ass D)) (trans (cong (comp D (comp D (right A f) (iden D))) (fid (L A))) (trans (idr D) (idr D))))) (lawb A f)))) ;
  law3 = λ{X}{Y}{Z}{f}{g} → trans (cong (HMap (R A)) (trans (cong (right A) (trans (sym (idr C)) (ass C))) (trans (natright A (iden C) (right A g) f) (cong (comp D (right A g)) (trans (cong (comp D (right A f)) (fid (L A))) (idr D)))))) (fcomp (R A))}

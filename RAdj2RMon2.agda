{-# OPTIONS --type-in-type #-}
module RAdj2RMon2 where

open import Function
open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors
open import Naturals
open import RMonads2
open import RAdjunctions2

open Cat
open Fun
open NatT
open RAdj

Adj2Mon : ∀{C D E}{J : Fun C D} → RAdj J E → RMonad J
Adj2Mon {C}{D}{E}{J} A = record{
  T    = OMap (R A) ∘ OMap (L A);
  η    = left A (iden E);
  bind = HMap (R A) ∘ right A;
  law1 = trans (cong (HMap (R A)) (lawa A (iden E))) (fid (R A));
  law2 = λ {_ _ f} → 
    trans (cong (comp D (HMap (R A) (right A f))) 
                (trans (sym (idr D)) 
                       (cong (comp D (left A (iden E))) (sym (fid J)))))
          (trans (natleft A (iden C) (right A f) (iden E)) 
                 (trans (cong (left A) 
                              (trans (cong (comp E (right A f)) 
                                           (trans (idl E) (fid (L A))))
                                     (idr E)))
                        (lawb A f)));
  law3 = λ{_ _ _ f g} → 
    trans (cong (HMap (R A)) 
                (trans (trans (cong (right A) 
                                    (cong (comp D (HMap (R A) (right A g))) 
                                          (trans (sym (idr D)) 
                                                 (cong (comp D f) 
                                                       (sym (fid J)))))) 
                              (trans (natright A (iden C) (right A g) f) 
                                     (trans (sym (ass E)) 
                                            (cong (comp E (comp E (right A g) 
                                                                  (right A f)))
                                                  (fid (L A)))))) 
                       (idr E))) 
          (fcomp (R A))}

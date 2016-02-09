module Lawvere where

open import Library
open import Categories
open import Categories.Sets
open import Categories.Initial
open import Categories.PushOuts
open import Categories.CoProducts
open import Functors
open import Functors.Fin

record Lawvere {a}{b} : Set (lsuc (a ⊔ b)) where
  constructor lawvere
  field T  : Cat {a}{b}
        L  : Fun Nats T
        L0 : Init T (Fun.OMap L zero)
        LP : ∀ m n →
          PushOut {C = T}{Fun.OMap L m}{Fun.OMap L n}{Fun.OMap L zero}
                  (Fun.HMap L (λ ())) (Fun.HMap L (λ ()))

LSet : Lawvere
LSet = lawvere
  Sets
  FinF
  (init (λ ()) (ext λ ()))
  λ m n → pushout
    (square (Fin (m + n)) extend  (lift m) (ext λ ()))
    (λ sq' → (sqmap (case m (Square.h sq') (Square.k sq'))
                    (ext (lem1 m (Square.h sq') (Square.k sq')))
                    (ext (lem2 m (Square.h sq') (Square.k sq'))))
             , λ u' → ext (sym ∘ lem3 m
                                      (Square.h sq')
                                      (Square.k sq')
                                      (SqMap.sqMor u')
                                      (SqMap.leftTr u')
                                      (SqMap.rightTr u') ))

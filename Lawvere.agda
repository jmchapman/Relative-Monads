module Lawvere where

open import Library
open import Categories
open import Categories.Sets
open import Categories.Initial
open import Categories.PushOuts
open import Categories.CoProducts
open import Categories.Terminal

open import Functors
open import Functors.Fin

record Lawvere {a}{b} : Set (lsuc (a ⊔ b)) where
  constructor lawvere
  field T  : Cat {a}{b}
        L  : Fun (Nats Op) T
        L0 : Term T (Fun.OMap L zero)
--        LP : ∀ m n →
--          PullBack {C = T}{Fun.OMap L m}{Fun.OMap L n}{Fun.OMap L zero}
--                  (Fun.HMap L (λ ())) (Fun.HMap L (λ ()))

FunOp : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → Fun C D → Fun (C Op) (D Op)
FunOp (functor OMap HMap fid fcomp) = functor OMap HMap fid fcomp

LSet : Lawvere
LSet = lawvere
  (Sets Op)
  (FunOp FinF)
  (term (λ ()) (ext λ ()))
--  λ m n → pushout
--    (square (Fin (m + n)) extend  (lift m) (ext λ ()))
--    (λ sq' → (sqmap (case m (Square.h sq') (Square.k sq'))
--                    (ext (lem1 m (Square.h sq') (Square.k sq')))
--                    (ext (lem2 m (Square.h sq') (Square.k sq'))))
--             , λ u' → ext (sym ∘ lem3 m
--                                      (Square.h sq')
--                                      (Square.k sq')
--                                     (SqMap.sqMor u')
--                                      (SqMap.leftTr u')
--                                      (SqMap.rightTr u') ))

open import RMonads
open import RMonads.RKleisli
open import RMonads.RKleisli.Functors

lem : RMonad FinF → Lawvere {lzero}{lzero}
lem T = lawvere
  (Kl T Op)
  (FunOp (RKlL T) )
  (term (λ ()) (ext λ ()))
{-  λ m n → pushout
    (square (m + n)
            (RMonad.η T ∘ extend)
            (RMonad.η T ∘ lift m)
            (ext λ ()))
    λ sq' →
      sqmap
        (case m (Square.h sq') (Square.k sq'))
        (ext λ i → trans (fcong (extend i) (RMonad.law2 T))
                         (lem1 m (Square.h sq') (Square.k sq') i) )
        (ext λ i → trans (fcong (lift m i) (RMonad.law2 T))
                         (lem2 m (Square.h sq') (Square.k sq') i))
      ,
      λ u' → ext λ i → sym $ lem3
        m
        (Square.h sq')
        (Square.k sq')
        (SqMap.sqMor u')
        (trans (ext λ i → fcong (extend i) (sym $ RMonad.law2 T))
               (SqMap.leftTr u'))
        (trans (ext λ i → fcong (lift m i) (sym $ RMonad.law2 T))
               (SqMap.rightTr u'))
        i
-}
open import Categories.Products

record Model {a}{b}{c}{d} (Law : Lawvere {a}{b}) : Set (lsuc (a ⊔ b ⊔ c ⊔ d)) where
  open Lawvere Law
  field C : Cat {c}{d}
        F : Fun T C
        X : Term C (Fun.OMap F (Fun.OMap L zero))

open import RMonads.REM
open import RMonads.CatofRAdj.InitRAdj
open import RMonads.CatofRAdj.TermRAdjObj

model : (T : RMonad FinF) → Model (lem T)
model T = record {
  C = EM T Op ;
  F = FunOp (K' T (EMObj T));
  X = term (λ{alg} → ralgmorph (RAlg.astr alg {0} (λ ()))
                               (λ {n}{f} →
                                 sym $ RAlg.alaw2 alg {n}{zero}{f}{λ ()} ))
           (λ{alg}{f} → RAlgMorphEq T (ext (λ t → trans
             (trans (cong (λ f₁ → RAlg.astr alg f₁ t) (ext (λ ())))
                    (sym (fcong t (RAlgMorph.ahom f {0}{RMonad.η T}))))
             (cong (RAlgMorph.amor f) (fcong t (RMonad.law1 T))))))}

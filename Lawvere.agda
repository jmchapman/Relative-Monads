module Lawvere where

open import Library
open import Data.Sum
open import Categories
open import Categories.Sets
open import Categories.Initial
open import Categories.PushOuts
open import Categories.Products hiding (_×_)
open import Categories.CoProducts
open import Categories.Terminal

open import Functors
open import Functors.Fin

record Lawvere {a}{b} : Set (lsuc (a ⊔ b)) where
  constructor lawvere
  field T  : Cat {a}{b}
        L  : Fun (Nats Op) T
        L0 : Term T (Fun.OMap L zero)
        LP : ∀ m n → Prod T (Fun.OMap L m) (Fun.OMap L n)

-- it's not the identity, it switches some implicit in fid and fcomp I think
FunOp : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} →
        Fun C D → Fun (C Op) (D Op)
FunOp (functor OMap HMap fid fcomp) = functor OMap HMap fid fcomp

LSet : Lawvere
LSet = lawvere
  (Sets Op)
  (FunOp FinF)
  (term (λ ()) (ext λ ()))
  λ m n → prod
    (Fin m ⊎ Fin n)
    inj₁
    inj₂
    [_,_]′
    refl
    refl
    λ p q → ext (λ{ (inj₁ a) -> fcong a p; (inj₂ b) -> fcong b q})

open import RMonads
open import RMonads.RKleisli
open import RMonads.RKleisli.Functors

lem : RMonad FinF → Lawvere {lzero}{lzero}
lem M = lawvere
  (Kl M Op)
  (FunOp (RKlL M) )
  (term (λ ()) (ext λ ()))
  λ m n → prod
    (m + n)
    (η ∘ extend)
    (η ∘ lift m)
    (case m)
    (ext λ i → trans (fcong (extend i) law2) (lem1 m _ _ i))
    (ext λ i → trans (fcong (lift m i) law2) (lem2 m _ _ i))
    λ {o} {f} {g} {h} p q → ext (lem3
      m
      f
      g
      h
      (trans (ext λ i → sym (fcong (extend i) law2)) p)
      (trans (ext λ i → sym (fcong (lift m i) law2)) q))
    where open RMonad M

open import Categories.Products

record Model {a}{b}{c}{d} (Law : Lawvere {a}{b}) : Set (lsuc (a ⊔ b ⊔ c ⊔ d))
  where
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

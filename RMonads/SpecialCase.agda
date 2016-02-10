module RMonads.SpecialCase where

open import Categories
open import Functors
open import Naturals hiding (Iso)
open import Monads
open import RMonads


leftM : ∀{a}{b}{C : Cat {a}{b}} → Monad C → RMonad (IdF C)
leftM M = record {
  T    = T;
  η    = η;
  bind = bind;
  law1 = law1;
  law2 = law2;
  law3 = law3} 
  where open Monad M

rightM : ∀{a b}{C : Cat {a}{b}} → RMonad (IdF C) → Monad C
rightM {C = C} M = record {
  T    = T;
  η    = η;
  bind = bind; 
  law1 = law1;
  law2 = law2;
  law3 = law3} where open RMonad M

open import Relation.Binary.HeterogeneousEquality
open import Isomorphism

isoM : ∀{a b}{C : Cat {a}{b}} → Iso (RMonad (IdF C)) (Monad C)
isoM = record {fun = rightM; inv = leftM; law1 = λ {(monad _ _ _ _ _ _) → refl}; law2 = λ {(rmonad _ _ _ _ _ _) → refl}}

open import Monads.MonadMorphs
open import RMonads.RMonadMorphs

leftMM : ∀{a b}{C : Cat {a}{b}}{M M' : Monad C} → MonadMorph M M' → 
         RMonadMorph (leftM M) (leftM M')
leftMM MM = record { 
  morph   = morph; 
  lawη    = lawη; 
  lawbind = lawbind} where open MonadMorph MM

rightMM : ∀{a b}{C : Cat {a}{b}}{M M' : RMonad (IdF C)} → RMonadMorph M M' → 
          MonadMorph (rightM M) (rightM M')
rightMM MM = record { 
  morph   = morph; 
  lawη    = lawη; 
  lawbind = lawbind} where open RMonadMorph MM


isoMM : ∀{a b}{C : Cat {a}{b}}{M M' : Monad C} → 
        Iso (RMonadMorph (leftM M) (leftM M')) (MonadMorph M M')
isoMM {M = monad _ _ _ _ _ _}{M' = monad _ _ _ _ _ _} = record { 
 fun  = rightMM;
 inv  = leftMM; 
 law1 = λ {(monadmorph _ _ _) → refl};
 law2 = λ {(rmonadmorph _ _ _) → refl}}

open import Adjunctions
open import RAdjunctions

leftA : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → Adj C D → RAdj (IdF C) D
leftA {C}{D} A = record{
  L        = L;
  R        = R;
  left     = left; 
  right    = right; 
  lawa     = lawa; 
  lawb     = lawb; 
  natleft  = natleft;
  natright = natright} where open Adj A

rightA : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → RAdj (IdF C) D → Adj C D
rightA {C = C}{D = D} A = record{
  L        = L;
  R        = R;
  left     = left; 
  right    = right; 
  lawa     = lawa; 
  lawb     = lawb; 
  natleft  = natleft;
  natright = natright} where open RAdj A

isoA : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} →
       Iso (RAdj (IdF C) D) (Adj C D)
isoA = record {
  fun = rightA;
  inv = leftA;
  law1 = λ {(adjunction _ _ _ _ _ _ _ _) → refl};
  law2 = λ {(radjunction _ _ _ _ _ _ _ _) → refl}}


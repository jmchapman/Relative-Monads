open import Categories
open import Monads

module Monads.Kleisli.Adjunction {a b}{C : Cat {a}{b}}(M : Monad C) where

open Cat C
open Monad M

open import Library
open import Functors
open import Monads.Kleisli
open import Adjunctions
open import Monads.Kleisli.Functors M
open Fun

KlAdj : Adj C (Kl M)
KlAdj = record {
  L        = KlL;
  R        = KlR;
  left     = id;
  right    = id;
  lawa     = λ _ → refl;
  lawb     = λ _ → refl;
  natleft  = lem;
  natright = lem}
  where 
   lem = λ {X}{X'}{Y}{Y'} (f : Hom X' X)(g : Hom Y (T Y')) h → 
    proof
    comp (bind g) (comp h f) 
    ≅⟨ cong (λ h → comp (bind g) (comp h f)) (sym law2) ⟩
    comp (bind g) (comp (comp (bind h) η) f) 
    ≅⟨ cong (comp (bind g)) ass ⟩
    comp (bind g) (comp (bind h) (comp η f)) 
    ∎

{-# OPTIONS --type-in-type #-}
open import Categories
open import Monads

module KleisliAdj {C}(M : Monad C) where

open Cat C
open Monad M

open import Function
open import Relation.Binary.HeterogeneousEquality
open  ≅-Reasoning renaming (begin_ to proof_)
open import Functors
open import Kleisli
open import Adjunctions
open import KleisliFunctors M
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

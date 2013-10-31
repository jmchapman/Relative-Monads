{-# OPTIONS --type-in-type #-}
module Fin where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Nat
open import Sets
open import Setoids
open import Categories
open import Functors
open import Isomorphism
open import FullyFaithful
open import Function
open import Data.Bool

open Cat
open Fun
open Iso
open import Data.Fin
open import Data.Nat

feq : ∀{n} → Fin n → Fin n → Bool
feq zero     zero     = true
feq zero     (suc j) = false
feq (suc i) zero     = false
feq (suc i) (suc j) = feq i j

Nats : Cat
Nats = record{
  Obj  = ℕ; 
  Hom  = λ m n → Fin m → Fin n;
  iden = id;
  comp = λ f g → f ∘ g;
  idl  = refl;
  idr  = refl;
  ass  = refl}

FinF : Fun Nats Sets
FinF = record {
  OMap  = Fin; 
  HMap  = id;
  fid   = refl;
  fcomp = refl}

FinFoid : Fun Nats Setoids
FinFoid = record {
  OMap  = λ n → record {
    set  = Fin n ; 
    eq   = λ i j → i ≅ j;
    ref  = refl; 
    sym' = sym;
    trn  = trans};
  HMap  = λ f → record {
    fun = f; feq = cong f};
  fid   = SetoidFunEq refl λ s s' → ext congid;
  fcomp = λ{_ _ _ f g} → 
    SetoidFunEq refl λ s s' → ext (congcomp f g)}

FinFF : FullyFaithful FinF
FinFF X Y = record {
  fun  = iden Sets; 
  inv  = iden Sets; 
  law1 = λ _ → refl;
  law2 = λ _ → refl}


{-# OPTIONS --type-in-type #-}
module Fin where

open import Utilities
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Nat
open import Sets
open import Setoids
open import Categories
open import Functors
open import Isomorphism
open import FullyFaithful
open import Booleans
open import Function

open Cat
open Fun
open Iso

data Fin : Nat → Set where
  fz : ∀{n} → Fin (s n)
  fs : ∀{n} → Fin n → Fin (s n)

feq : ∀{n} → Fin n → Fin n → Bool
feq fz     fz     = tt
feq fz     (fs j) = ff
feq (fs i) fz     = ff
feq (fs i) (fs j) = feq i j

Nats : Cat
Nats = record{
  Obj  = Nat; 
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
  fid   = SetoidFunEq refl λ s s' → ext respid;
  fcomp = λ{_ _ _ f g} → 
    SetoidFunEq refl λ s s' → ext (respcomp f g)}

FinFF : FullyFaithful FinF
FinFF X Y = record {
  fun  = iden Sets; 
  inv  = iden Sets; 
  law1 = λ _ → refl;
  law2 = λ _ → refl}


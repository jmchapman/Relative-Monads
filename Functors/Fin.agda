module Functors.Fin where

open import Library
open import Categories.Sets
open import Categories.Setoids
open import Categories
open import Functors
open import Isomorphism
open import Functors.FullyFaithful

open Cat
open Fun
open Iso
open import Data.Fin
open import Data.Nat

Nats : Cat {lzero}{lzero}
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
  fun  = id;
  inv  = id;
  law1 = λ _ → refl;
  law2 = λ _ → refl}

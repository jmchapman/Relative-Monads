module FunctorCat where

open import Categories
open import Functors
open import Naturals

FunctorCat : ∀{a b c d} → Cat {a}{b} → Cat {c}{d} → Cat
FunctorCat C D = record{
  Obj  = Fun C D;
  Hom  = NatT;
  iden = idNat;
  comp = compNat;
  idl  = idlNat;
  idr  = idrNat;
  ass  = λ{_}{_}{_}{_}{α}{β}{η} → assNat {α = α}{β}{η}}

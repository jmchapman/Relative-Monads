{-# OPTIONS --type-in-type #-}
module FunctorCat where

open import Categories
open import Functors
open import Naturals

FunctorCat : Cat → Cat → Cat
FunctorCat C D = record{
  Obj  = Fun C D;
  Hom  = NatT;
  iden = idNat;
  comp = compNat;
  idl  = idlNat;
  idr  = idrNat;
  ass  = λ{_}{_}{_}{_}{α}{β}{η} → assNat {_}{_}{_}{_}{_}{_}{α}{β}{η}}

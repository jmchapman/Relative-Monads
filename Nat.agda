{-# OPTIONS --type-in-type #-}
module Nat where

open import Booleans

data Nat : Set where
  z : Nat
  s : Nat → Nat

neq : Nat → Nat → Bool
neq z     z     = tt
neq z     (s n) = ff
neq (s m) z     = ff
neq (s m) (s n) = neq m n

_+_ : Nat → Nat → Nat
z   + n = n
s m + n = s (m + n)
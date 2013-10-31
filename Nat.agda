{-# OPTIONS --type-in-type #-}
module Nat where

open import Data.Bool

data Nat : Set where
  z : Nat
  s : Nat → Nat

neq : Nat → Nat → Bool
neq z     z     = true
neq z     (s n) = false
neq (s m) z     = false
neq (s m) (s n) = neq m n

_+_ : Nat → Nat → Nat
z   + n = n
s m + n = s (m + n)

{-# OPTIONS --type-in-type #-}
module Nat where

open import Data.Nat
open import Data.Bool

neq : ℕ → ℕ → Bool
neq zero     zero     = true
neq zero     (suc n) = false
neq (suc m) zero     = false
neq (suc m) (suc n) = neq m n


{-# OPTIONS --type-in-type #-}
module Monoids where

open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Data.Nat

record Monoid : Set where
  field S   : Set
        ε   : S
        _•_ : S → S → S
        lid : ∀{m} → ε • m ≅ m
        rid : ∀{m} → m • ε ≅ m
        ass : ∀{m n o} → (m • n) • o ≅ m • (n • o)

rid+ : ∀{n} → n + zero ≅ n
rid+ {zero}   = refl
rid+ {suc n} = cong suc (rid+ {n})

ass+ : ∀{m n o} → (m + n) + o ≅ m + (n + o)
ass+ {zero}   = refl
ass+ {suc m} = cong suc (ass+ {m})

Nat+Mon : Monoid 
Nat+Mon = record { 
  S   = ℕ; 
  ε   = zero; 
  _•_ = _+_;
  lid = refl; 
  rid = rid+; 
  ass = λ{m} → ass+ {m}}


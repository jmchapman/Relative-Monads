{-# OPTIONS --type-in-type #-}
module Monoids where

open import Equality
open import Nat

record Monoid : Set where
  field S   : Set
        ε   : S
        _•_ : S → S → S
        lid : ∀{m} → ε • m ≅ m
        rid : ∀{m} → m • ε ≅ m
        ass : ∀{m n o} → (m • n) • o ≅ m • (n • o)

rid+ : ∀{n} → n + z ≅ n
rid+ {z}   = refl
rid+ {s n} = resp s (rid+ {n})

ass+ : ∀{m n o} → (m + n) + o ≅ m + (n + o)
ass+ {z}   = refl
ass+ {s m} = resp s (ass+ {m})

Nat+Mon : Monoid 
Nat+Mon = record { 
  S   = Nat; 
  ε   = z; 
  _•_ = _+_;
  lid = refl; 
  rid = rid+; 
  ass = λ{m} → ass+ {m}}


module Monoids where

open import Library

record Monoid {a} : Set (lsuc a) where
  field S   : Set a
        ε   : S
        _•_ : S → S → S
        lid : ∀{m} → ε • m ≅ m
        rid : ∀{m} → m • ε ≅ m
        ass : ∀{m n o} → (m • n) • o ≅ m • (n • o)

  infix 10 _•_

Nat+Mon : Monoid 
Nat+Mon = record { 
  S   = ℕ; 
  ε   = zero; 
  _•_ = _+_;
  lid = refl; 
  rid = ≡-to-≅ $ +-right-identity _; 
  ass = λ{m} → ≡-to-≅ $ +-assoc m _ _}


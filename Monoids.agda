module Monoids where

open import Library

record Monoid {a} : Set (lsuc a) where
  field S   : Set a
        ε   : S
        _•_ : S → S → S
        lid : ∀{m} → ε • m ≅ m
        rid : ∀{m} → m • ε ≅ m
        ass : ∀{m n o} → (m • n) • o ≅ m • (n • o)

rid+ : ∀{n} → n + zero ≅ n
rid+ {zero}  = refl
rid+ {suc n} = cong suc (rid+ {n})

ass+ : ∀{m n o} → (m + n) + o ≅ m + (n + o)
ass+ {zero}  = refl
ass+ {suc m} = cong ℕ.suc (ass+ {m})

Nat+Mon : Monoid 
Nat+Mon = record { 
  S   = ℕ; 
  ε   = zero; 
  _•_ = _+_;
  lid = refl; 
  rid = rid+; 
  ass = λ{m} → ass+ {m}}


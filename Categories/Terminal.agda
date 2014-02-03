{-# OPTIONS --type-in-type #-}
module Categories.Terminal where

open import Library
open import Categories
open import Categories.Sets
open Cat

record Term (C : Cat) : Set where
  field T : Obj C
        t : ∀{X} → Hom C X T
        law : ∀{X}{f : Hom C X T} → t {X} ≅ f

OneSet : Term Sets
OneSet = record {T = ⊤; t = λ _ → _; law = ext (λ _ → refl)}

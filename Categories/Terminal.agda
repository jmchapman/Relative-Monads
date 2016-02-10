module Categories.Terminal where

open import Library
open import Categories
open import Categories.Sets
open Cat

record Term {a b} (C : Cat {a}{b})(T : Obj C) : Set (a ⊔ b) where
  constructor term
  field t : ∀{X} → Hom C X T
        law : ∀{X}{f : Hom C X T} → t {X} ≅ f

OneSet : Term Sets ⊤
OneSet = record {t = λ _ → _; law = ext (λ _ → refl)}

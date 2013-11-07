{-# OPTIONS --type-in-type #-}
module Terminal where

open import Categories
open import Relation.Binary.HeterogeneousEquality
open import Equality
open import Sets
open import Data.Unit
open Cat

record Term (C : Cat) : Set where
  field T : Obj C
        t : ∀{X} → Hom C X T
        law : ∀{X}{f : Hom C X T} → t {X} ≅ f

OneSet : Term Sets
OneSet = record {T = ⊤; t = λ _ → _; law = ext (λ _ → refl)}

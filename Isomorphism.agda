module Isomorphism where

open import Library

record Iso {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≅ b
        law2 : ∀ a → inv (fun a) ≅ a

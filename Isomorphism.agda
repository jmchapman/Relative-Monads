{-# OPTIONS --type-in-type #-}
module Isomorphism where

open import Relation.Binary.HeterogeneousEquality

record Iso (A B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≅ b
        law2 : ∀ a → inv (fun a) ≅ a

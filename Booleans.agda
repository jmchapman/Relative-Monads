module Booleans where

data Bool : Set where
  tt ff : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if_then_else_ tt a a' = a
if_then_else_ ff a a' = a'
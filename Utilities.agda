module Utilities where

{-
_•_ : {A B C : Set} → (B → C) → (A → B) → A → C
f • g = λ a → f (g a)
-}

{-
_•_ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} → 
      (∀{a} b → C a b) → (g : (∀ a → B a)) → ∀ a → C a (g a)
f • g = λ a → f (g a)

id : {A : Set} → A → A
id a = a

data Zero : Set where

record One : Set where
  constructor []

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst
-}

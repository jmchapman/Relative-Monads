{-# OPTIONS --type-in-type #-}
module Monads2 where

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories

record Monad (C : Cat) : Set where
  open Cat C
  field T    : Obj → Obj
        η    : ∀ {X} → Hom X (T X)
        bind : ∀{X Y} → Hom X (T Y) → Hom (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden {T X}
        law2 : ∀{X Y}{f : Hom X (T Y)} → comp (bind f) η ≅ f
        law3 : ∀{X Y Z}{f : Hom X (T Y)}{g : Hom Y (T Z)} → 
               bind (comp (bind g) f)  ≅ comp (bind g) (bind f)

open import Functors

TFun : ∀{C} → Monad C → Fun C C
TFun {C} M = let open Monad M; open Cat C in record { 
  OMap  = T; 
  HMap  = bind ∘ comp η; 
  fid   = 
    proof 
    bind (comp η iden)
    ≅⟨ cong bind idr ⟩
    bind η
    ≅⟨ law1 ⟩ 
    iden ∎; 
  fcomp = λ {_}{_}{_}{f}{g} → 
    proof
    bind (comp η (comp f g))
    ≅⟨ cong bind (sym ass) ⟩
    bind (comp (comp η f) g)
    ≅⟨ cong (λ f → bind (comp f g)) (sym law2) ⟩
    bind (comp (comp (bind (comp η f)) η) g)
    ≅⟨ cong bind ass ⟩
    bind (comp (bind (comp η f)) (comp η g))
    ≅⟨ law3 ⟩
    comp (bind (comp η f)) (bind (comp η g))
    ∎}

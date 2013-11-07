{-# OPTIONS --type-in-type #-}
module Monads2 where


open import Relation.Binary.HeterogeneousEquality
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
TFun {C} M = record { 
  OMap  = T; 
  HMap  = λ f → bind(comp η f); 
  fid   = trans (cong bind idr) law1; 
  fcomp = λ {_} {_} {_} {f} {g} → trans (cong bind (trans (trans (sym ass) (cong (λ f → comp f g) (sym law2))) ass)) law3}
  where open Monad M; open Cat C

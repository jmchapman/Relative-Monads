{-# OPTIONS --type-in-type #-}
module RMonads2 where

open import Relation.Binary.HeterogeneousEquality
open import Categories
open import Functors

open Cat
open Fun

record RMonad {C D : Cat}(J : Fun C D) : Set where
  field T    : Obj C → Obj D
        η    : ∀{X} → Hom D (OMap J  X) (T X)
        _* : ∀{X Y} → Hom D (OMap J X) (T Y) → Hom D (T X) (T Y)
        law1 : ∀{X} → η {X} * ≅ iden D {T X}
        law2 : ∀{X Y}{f : Hom D (OMap J X) (T Y)} → comp D (f *) η ≅ f
        law3 : ∀{X Y Z}
               {f : Hom D (OMap J X) (T Y)}{g : Hom D (OMap J Y) (T Z)} →
               (comp D (g *) f) * ≅ comp D (g *) (f *)

  bind = λ{X}{Y} → _* {X}{Y}

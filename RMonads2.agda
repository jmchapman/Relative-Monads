{-# OPTIONS --type-in-type #-}
module RMonads2 where

open import Equality
open import Categories
open import Functors

open Cat
open Fun

record RMonad {C D : Cat}(J : Fun C D) : Set where
  field T    : ! C ! → ! D !
        η    : ∀{X} → D < J ` X , T X >
        _* : ∀{X Y} → D < J ` X , T Y > → D < T X , T Y >                                                                    
        law1 : ∀{X} → η {X} * ≅ iden D {T X}
        law2 : ∀{X Y}{f : D < J ` X , T Y >} → D ! f * • η ≅ f
        law3 : ∀{X Y Z}
               {f : D < J ` X , T Y >}{g : D < J ` Y , T Z >} →
               (D ! g * • f) *  ≅ D ! g * • f *

  bind = λ{X}{Y} → _* {X}{Y}
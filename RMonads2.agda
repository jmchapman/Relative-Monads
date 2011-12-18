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
        bind : ∀{X Y} → D < J ` X , T Y > → D < T X , T Y >                                                                    
        law1 : ∀{X} → bind (η {X}) ≅ iden D {T X}
        law2 : ∀{X Y}{f : D < J ` X , T Y >} → D ! bind f • η ≅ f
        law3 : ∀{X Y Z}
               {f : D < J ` X , T Y >}{g : D < J ` Y , T Z >} →
               bind (D ! bind g • f)  ≅ D ! bind g • bind f

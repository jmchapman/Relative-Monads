module RMonads.CatofRMonads where

open import Categories
open import Functors
open import RMonads
open import RMonads.RMonadMorphs

CatofRMonads : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}(J : Fun C D) → Cat
CatofRMonads J = record
                 { Obj  = RMonad J
                 ; Hom  = RMonadMorph
                 ; iden = IdRMonadMorph _
                 ; comp = CompRMonadMorph
                 ; idl  = idl _
                 ; idr  = idr _
                 ; ass  = λ{_ _ _ _ f g h} → ass f g h
                 }

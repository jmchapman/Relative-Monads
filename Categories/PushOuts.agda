module Categories.PushOuts where

open import Library
open import Categories

open Cat

record Square {a}{b}{C : Cat {a}{b}}{X Y Z}(f : Hom C Z X)(g : Hom C Z Y) : Set (a ⊔ b) where
  constructor square
  field W    : Obj C
        h    : Hom C X W
        k    : Hom C Y W
        scom : comp C h f ≅ comp C k g

record SqMap {a}{b}{C : Cat {a}{b}}{X Y Z : Obj C}{f : Hom C Z X}{g : Hom C Z Y}
             (sq sq' : Square {a}{b}{C} f g) : Set (a ⊔ b) where
  constructor sqmap
  open Square
  field sqMor     : Hom C (W sq) (W sq')
        leftTr   : comp C sqMor (h sq) ≅ h sq'
        rightTr  : comp C sqMor (k sq) ≅ k sq'
open SqMap

record PushOut {a}{b}{C : Cat {a}{b}}{X Y Z}(f : Hom C Z X)(g : Hom C Z Y) : Set (a ⊔ b) where
  constructor pushout
  field sq : Square {a}{b}{C} f g
        uniqPush : (sq' : Square f g) → Σ (SqMap sq sq')
          \ u → (u' : SqMap sq sq') → sqMor u ≅ sqMor u'
          

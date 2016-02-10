module Categories.Products where

open import Library renaming (_×_ to Pair) hiding ([_])
open import Categories

_×_ : ∀{l l' m m'}(C : Cat {l}{m})(D : Cat {l'}{m'}) -> Cat
C × D = record
          { Obj  = Pair (Obj C) (Obj D)
          ; Hom  = λ {(X , X') (Y , Y') -> Pair (Hom C X Y) (Hom D X' Y')}
          ; iden = iden C , iden D
          ; comp = λ {(f , f') (g , g') -> comp C f g , comp D f' g'}
          ; idl  = cong₂ _,_ (idl C) (idl D)
          ; idr  = cong₂ _,_ (idr C) (idr D)
          ; ass  = cong₂ _,_ (ass C) (ass D)
          } where open Cat

infixr 50 _×_

record Prod {l}{m}(C : Cat {l}{m})(A : Cat.Obj C)(B : Cat.Obj C) : Set (l ⊔ m)
  where
  constructor prod
  open Cat C
  field Pr : Obj
        π₁ : Hom Pr A
        π₂ : Hom Pr B
        [_,_] : ∀{C} → Hom C A → Hom C B → Hom C Pr
        law1 : ∀{C}{f : Hom C A}{g} → comp π₁ [ f , g ] ≅ f
        law2 : ∀{C}{f : Hom C A}{g} → comp π₂ [ f , g ] ≅ g
        law3 : ∀{C}{f : Hom C A}{g : Hom C B}{h : Hom C Pr} →
               comp π₁ h ≅ f → comp π₂ h ≅ g → h ≅ [ f , g ]

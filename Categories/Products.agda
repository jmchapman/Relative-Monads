module Categories.Products where

open import Library renaming (_×_ to Pair)
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

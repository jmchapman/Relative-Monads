{-# OPTIONS --type-in-type #-}
module RMonads where

open import Library
open import Categories
open import Functors

open Fun

record RMonad {C D : Cat}(J : Fun C D) : Set where
  open Cat
  field T    : Obj C → Obj D
        η    : ∀{X} → Hom D (OMap J  X) (T X)
        bind : ∀{X Y} → Hom D (OMap J X) (T Y) → Hom D (T X) (T Y)
        law1 : ∀{X} → bind (η {X}) ≅ iden D {T X}
        law2 : ∀{X Y}{f : Hom D (OMap J X) (T Y)} → comp D (bind f) η ≅ f
        law3 : ∀{X Y Z}
               {f : Hom D (OMap J X) (T Y)}{g : Hom D (OMap J Y) (T Z)} →
               bind (comp D (bind g) f) ≅ comp D (bind g) (bind f)

open import Functors

TFun : ∀{C D}{J : Fun C D} → RMonad J → Fun C D
TFun {C}{D}{J} M = let open RMonad M; open Cat in record { 
  OMap  = T; 
  HMap  = bind ∘ comp D η ∘ HMap J; 
  fid   = 
    proof 
    bind (comp D η (HMap J (iden C)))
    ≅⟨ cong (bind ∘ comp D η) (fid J) ⟩ 
    bind (comp D η (iden D))
    ≅⟨ cong bind (idr D) ⟩ 
    bind η
    ≅⟨ law1 ⟩ 
    iden D 
    ∎;
  fcomp = λ{X}{Y}{Z}{f}{g} → 
    proof
    bind (comp D η (HMap J (comp C f g))) 
    ≅⟨ cong (bind ∘ comp D η) (fcomp J) ⟩
    bind (comp D η (comp D (HMap J f) (HMap J g)))
    ≅⟨ cong bind (sym (ass D)) ⟩
    bind (comp D (comp D η (HMap J f)) (HMap J g))
    ≅⟨ cong (λ f → bind (comp D f (HMap J g))) (sym law2) ⟩
    bind (comp D (comp D (bind (comp D η (HMap J f))) η) (HMap J g))
    ≅⟨ cong bind (ass D) ⟩
    bind (comp D (bind (comp D η (HMap J f))) (comp D η (HMap J g)))
    ≅⟨ law3 ⟩
    comp D (bind (comp D η (HMap J f))) (bind (comp D η (HMap J g)))
    ∎}

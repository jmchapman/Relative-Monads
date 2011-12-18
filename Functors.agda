{-# OPTIONS --type-in-type #-}
module Functors where

open import Utilities
open import Equality
open import Categories
open Cat

record Fun (C D : Cat) : Set where
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)
open Fun

_`_ : ∀{C D}(F : Fun C D) → Obj C → Obj D
F ` X = OMap F X

IdF : ∀ C → Fun C C
IdF C = record{OMap = id;HMap = id;fid = refl;fcomp = refl}

_○_ : ∀{C D E} → Fun D E → Fun C D → Fun C E
_○_ {C}{D}{E} F G = record{OMap  = λ X → OMap F (OMap G X);
                          HMap   = λ f → HMap F (HMap G f);
                          fid    = begin 
                                   HMap F (HMap G (iden C)) 
                                   ≅⟨ resp (HMap F) (fid G) ⟩
                                   HMap F (iden D)
                                   ≅⟨ fid F ⟩ 
                                   iden E 
                                   ∎;
                          fcomp  = λ {X}{Y}{Z}{f}{g} → 
                                   begin
                                   HMap F (HMap G (comp C f g)) 
                                   ≅⟨ resp (HMap F) (fcomp G)  ⟩ 
                                   HMap F (comp D (HMap G f) (HMap G g))
                                   ≅⟨ fcomp F ⟩ 
                                   comp E (HMap F (HMap G f)) (HMap F (HMap G g)) 
                                    ∎}

FunctorEq : ∀{C D}(F G : Fun C D) → 
            OMap F ≅ OMap G → 
            (∀{X Y}(f : Hom C X Y) → HMap F f ≅ HMap G f) → 
            F ≅ G
FunctorEq {C}{D} F G p q = funnyresp4'
  {Obj C → Obj D}
  {λ OMap → ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)}
  {λ OMap HMap → ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}}
  {λ OMap HMap → ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → HMap (comp C f g) ≅ comp D (HMap f) (HMap g)}
  p
  (iext λ X → iext λ Y → ext λ f → q f)
  (iext λ X → fixtypes 
    (q (iden C))
    (iresp (λ {X} → iden D {X}) (fresp X p)))
  (iext λ X → iext λ Y → iext λ Z → iext λ f → iext λ g → fixtypes 
    (q (comp C f g)) 
    (trans (trans (sym (fcomp F)) (q (comp C f g))) (fcomp G)))
  λ w x y z → record{OMap = w;HMap = x;fid = y; fcomp = z} 
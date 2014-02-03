module Functors where

open import Library
open import Categories
open Cat

record Fun {a b c d} (C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d) where
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)
open Fun

IdF : ∀{a b}(C : Cat {a}{b}) → Fun C C
IdF C = record{OMap = id;HMap = id;fid = refl;fcomp = refl}

_○_ : ∀{a b}{C D E : Cat {a}{b}} → Fun D E → Fun C D → Fun C E
_○_ {C = C}{D = D}{E = E} F G = record{
  OMap  = λ X → OMap F (OMap G X);
  HMap   = λ f → HMap F (HMap G f);
  fid    = 
    proof
    HMap F (HMap G (iden C)) 
    ≅⟨ cong (HMap F) (fid G) ⟩
    HMap F (iden D)
    ≅⟨ fid F ⟩ 
    iden E 
    ∎;
  fcomp  = λ {X}{Y}{Z}{f}{g} → 
    proof
    HMap F (HMap G (comp C f g)) 
    ≅⟨ cong (HMap F) (fcomp G)  ⟩ 
    HMap F (comp D (HMap G f) (HMap G g))
    ≅⟨ fcomp F ⟩ 
    comp E (HMap F (HMap G f)) (HMap F (HMap G g)) 
    ∎}


FunctorEq : ∀{C D}(F G : Fun C D) → 
            OMap F ≅ OMap G → 
            (∀{X Y}(f : Hom C X Y) → HMap F f ≅ HMap G f) → 
            F ≅ G
FunctorEq {C}{D} F G p q = funnycong4'
  {Obj C → Obj D}
  {λ OMap → ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)}
  {λ OMap HMap → ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}}
  {λ OMap HMap → ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
     HMap (comp C f g) ≅ comp D (HMap f) (HMap g)}
  (proof 
   OMap F 
   ≅⟨ p ⟩ 
   OMap G 
   ∎)
  (iext λ X → iext λ Y → ext λ f → 
    proof 
    HMap F f 
    ≅⟨ q f ⟩ 
    HMap G f ∎)
  (iext λ X → fixtypes (
    proof 
    iden D {OMap F X} 
    ≅⟨ sym (fid F) ⟩ 
    HMap F (iden C) 
    ≅⟨ q (iden C) ⟩ 
    HMap G (iden C) 
    ∎))
  (iext λ X → iext λ Y → iext λ Z → iext λ f → iext λ g → fixtypes (
    proof 
    comp D (HMap F f) (HMap F g) 
    ≅⟨ sym (fcomp F) ⟩ 
    HMap F (comp C f g)
    ≅⟨ q (comp C f g) ⟩ 
    HMap G (comp C f g)
    ∎))
  λ w x y z → record{OMap = w;HMap = x;fid = y; fcomp = z} 


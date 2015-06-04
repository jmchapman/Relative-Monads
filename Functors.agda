module Functors where

open import Library
open import Categories
open Cat

record Fun {a b c d} (C : Cat {a}{b})(D : Cat {c}{d}) : Set (a ⊔ b ⊔ c ⊔ d) 
  where
  constructor functor
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≅ comp D (HMap f) (HMap g)
open Fun

IdF : ∀{a b}(C : Cat {a}{b}) → Fun C C
IdF C = record{OMap = id;HMap = id;fid = refl;fcomp = refl}

_○_ : ∀{a b c d e f}{C : Cat {a}{b}}{D : Cat {c}{d}}{E : Cat {e}{f}} → 
      Fun D E → Fun C D → Fun C E
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
infix 10 _○_

FunctorEq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}(F G : Fun C D) → 
            OMap F ≅ OMap G → 
            (∀{X Y}(f : Hom C X Y) → HMap F f ≅ HMap G f) → 
            F ≅ G
FunctorEq {D = D}(functor fo fh fp fp') (functor .fo gh gp gp') refl q =
  cong₃ (functor fo)
        (iext (λ _ → iext (λ _ → ext q)))
        (iext (λ _ → fixtypes' refl))
        (iext (λ _ → iext (λ _ → iext (λ _ → iext (λ k → iext (λ l → fixtypes' (cong₂ (comp D) (q k) (q l)))))))) 

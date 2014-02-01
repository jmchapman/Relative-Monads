{-# OPTIONS --type-in-type #-}
open import Categories
open import Functors
open import RMonads

module RMonads.REM {C D : Cat}{J : Fun C D}(M : RMonad J) where

open RMonad M

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Equality

open Fun

record RAlg : Set where
  open Cat D
  field acar  : Obj
        astr  : ∀ {Z} → Hom (OMap J Z) acar → Hom (T Z) acar
        alaw1 : ∀ {Z}{f : Hom (OMap J Z) acar} →
                f ≅ comp (astr f) η
        alaw2 : ∀{Z}{W}{k : Hom (OMap J Z) (T W)}
                {f : Hom (OMap J W) acar} →
                astr (comp (astr f) k) ≅ comp (astr f) (bind k)

AlgEq : {X Y : RAlg} → RAlg.acar X ≅ RAlg.acar Y → 
  (∀ Z → RAlg.astr X {Z} ≅ RAlg.astr Y {Z}) → 
        X ≅ Y
AlgEq {X}{Y} p q = let open Cat; open RAlg in funnycong4 
  {Obj D}
  {λ acar → ∀{Z} → Hom D (OMap J Z) acar → Hom D (T Z) acar}
  {λ acar astr → ∀{Z} {f : Hom D (OMap J Z) acar} → f ≅ comp D (astr f) η}
  {λ acar astr _ → ∀{Z W}
    {k : Hom D (OMap J Z) (T W)}{f : Hom D (OMap J W) acar} →
    astr (comp D (astr f) k) ≅ comp D (astr f) (bind k)}
  {RAlg}
  (λ x y z z' → record { acar = x; astr = y; alaw1 = z; alaw2 = z' })
  p 
  (iext q)
  (iext λ Z → diext λ {a}{a'} r → fixtypes (
    proof 
    comp D (astr X a) η 
    ≅⟨ sym (alaw1 X) ⟩
    a
    ≅⟨ r ⟩ 
    a' 
    ∎))
  (iext λ Z → iext λ W → iext λ k → diext λ {a}{a'} r → fixtypes (
    proof
    comp D (astr X a) (bind k) 
    ≅⟨ cong₂ (λ Ran f → comp D {T Z} {T W} {Ran} f (bind k)) 
             p 
             (dcong r 
                    (dext (λ _ → cong (Hom D (T W)) p)) 
                    (q W)) ⟩
    comp D (astr Y a') (bind k)
    ≅⟨ sym (alaw2 Y) ⟩
    astr Y (comp D (astr Y a') k) 
    ∎)) 

astrnat : ∀(alg : RAlg){X Y}
          (f : Cat.Hom C X Y) → 
          (g : Cat.Hom D (OMap J X) (RAlg.acar alg))
          (g' : Cat.Hom D (OMap J Y) (RAlg.acar alg)) →
          Cat.comp D g' (HMap J f) ≅ g → 
          Cat.comp D (RAlg.astr alg g') 
                     (RMonad.bind M (Cat.comp D (RMonad.η M) (HMap J f))) 
          ≅ 
          RAlg.astr alg g
astrnat alg f g g' p = let 
  open RAlg alg; open Cat D in
  proof
  comp (astr g') (bind (comp η (HMap J f))) 
  ≅⟨ sym alaw2 ⟩
  astr (comp (astr g') (comp η (HMap J f)))
  ≅⟨ cong astr (sym ass) ⟩
  astr (comp (comp (astr g') η) (HMap J f))
  ≅⟨ cong (λ g₁ → astr (comp g₁ (HMap J f))) (sym alaw1) ⟩ 
  astr (comp g' (HMap J f))
  ≅⟨ cong astr p ⟩
  astr g ∎

record RAlgMorph (A B : RAlg) : Set 
  where
  open Cat D
  open RAlg
  field amor : Hom (acar A) (acar B)
        ahom : ∀{Z}{f : Hom (OMap J Z) (acar A)} → 
               comp amor (astr A f) ≅ astr B (comp amor f)
open RAlgMorph

RAlgMorphEq : ∀{X Y : RAlg}{f g : RAlgMorph X Y} → amor f ≅ amor g → f ≅ g
RAlgMorphEq {X}{Y}{f}{g} p = let open Cat D; open RAlg in funnycong
  {Cat.Hom D (RAlg.acar X) (RAlg.acar Y)}
  {λ amor → ∀{Z}{f : Hom (OMap J Z) (acar X)} → 
              comp amor (astr X f) ≅ astr Y (comp amor f)}
  p
  (iext λ Z → iext λ h → fixtypes (
    proof
    astr Y (comp (amor f) h) 
    ≅⟨ sym (ahom f) ⟩ 
    comp (amor f) (astr X h) 
    ≅⟨ cong (λ f₁ → comp f₁ (astr X h)) p ⟩ 
    comp (amor g) (astr X h) 
    ∎))
  λ x y → record{amor = x;ahom = y} 

lemZ : ∀{X X' Y Y' : RAlg}
       {f : RAlgMorph X Y}{g : RAlgMorph X' Y'} → X ≅ X' → Y ≅ Y' → 
             amor f ≅ amor g → f ≅ g
lemZ refl refl = RAlgMorphEq

IdMorph : ∀{A : RAlg} → RAlgMorph A A
IdMorph {A} = let open Cat D; open RAlg A in record {
  amor = iden;
  ahom = λ {Z} {f} → 
    proof 
    comp iden (astr f)
    ≅⟨ idl ⟩ 
    astr f
    ≅⟨ cong astr (sym idl) ⟩ 
    astr (comp iden f) 
    ∎}

CompMorph : ∀{X Y Z : RAlg} → 
            RAlgMorph Y Z → RAlgMorph X Y → RAlgMorph X Z
CompMorph {X}{Y}{Z} f g = let open Cat D; open RAlg in record {
  amor = comp (amor f) (amor g);
  ahom = λ {Z₁} {f'} → 
    proof
    comp (comp (amor f) (amor g)) (astr X f') 
    ≅⟨ ass ⟩
    comp (amor f) (comp (amor g) (astr X f'))
    ≅⟨ cong (comp (amor f)) (ahom g) ⟩
    comp (amor f) (astr Y (comp (amor g) f'))
    ≅⟨ ahom f ⟩
    astr Z (comp (amor f) (comp (amor g) f'))
    ≅⟨ cong (astr Z) (sym ass) ⟩
    astr Z (comp (comp (amor f) (amor g)) f') 
    ∎}

idlMorph : {X Y : RAlg}{f : RAlgMorph X Y} →
           CompMorph IdMorph f ≅ f
idlMorph = RAlgMorphEq (Cat.idl D)

idrMorph : ∀{X Y : RAlg}{f : RAlgMorph X Y} →
           CompMorph f IdMorph ≅ f
idrMorph = RAlgMorphEq (Cat.idr D) 

assMorph : ∀{W X Y Z : RAlg}
           {f : RAlgMorph Y Z}{g : RAlgMorph X Y}{h : RAlgMorph W X} →
           CompMorph (CompMorph f g) h ≅ CompMorph f (CompMorph g h)
assMorph = RAlgMorphEq (Cat.ass D)

EM : Cat
EM = record{
  Obj  = RAlg;
  Hom  = RAlgMorph;
  iden = IdMorph;
  comp = CompMorph;
  idl  = idlMorph;
  idr  = idrMorph;
  ass  = λ{_}{_}{_}{_}{f}{g}{h} → assMorph {_}{_}{_}{_}{f}{g}{h}}


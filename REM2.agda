{-# OPTIONS --type-in-type #-}
module REM2 where

open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Equality
open import Categories
open import Functors
open import RMonads2

open Fun

record RAlg {C D : Cat}{J : Fun C D}(M : RMonad J) : Set where
  open Cat D
  open RMonad M 
  field acar  : Obj
        astr  : ∀ {Z} → Hom (OMap J Z) acar → Hom (T Z) acar
        alaw1 : ∀ {Z}{f : Hom (OMap J Z) acar} →
                f ≅ comp (astr f) η
        alaw2 : ∀{Z}{W}{k : Hom (OMap J Z) (T W)}
                {f : Hom (OMap J W) acar} →
                astr (comp (astr f) k) ≅ comp (astr f) (bind k)


AlgEq : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M} → RAlg.acar X ≅ RAlg.acar Y → 
  (∀ Z → RAlg.astr X {Z} ≅ RAlg.astr Y {Z}) → 
        X ≅ Y
AlgEq {C}{D}{J}{M}{X}{Y} p q = let open Cat; open RAlg; open RMonad in funnycong4 
  {Obj D}
  {λ acar₁ → {Z : _} → Hom D (OMap J Z) acar₁ → Hom D (T M Z) acar₁}
  {λ acar₁ astr₁ → {Z : _} {f : Hom D (OMap J Z) acar₁} → 
     f ≅ comp D (astr₁ f) (η M)}
  {λ acar₁ astr₁ _ → {Z W : _} 
     {k : Hom D (OMap J Z) (T M W)} {f : Hom D (OMap J W) acar₁} →
     astr₁ (comp D (astr₁ f) k) ≅ comp D (astr₁ f) (bind M k)}
  {RAlg {C}{D}{J} M}
  (λ x y z z' → record { acar = x; astr = y; alaw1 = z; alaw2 = z' })
  p 
  (iext q)
  (iext (λ Z → diext (λ {f} {f'} r → fixtypes (trans (sym (alaw1 X)) r))))
  (iext (λ Z → iext (λ W → iext (λ k → diext (λ {f} {f'} r → fixtypes (trans (cong₂ (λ Ran f₁ → comp D {T M Z} {T M W} {Ran} f₁ (bind M k)) p (dcong r (dext (λ _ → cong (Hom D (T M W)) p)) (q W))) (sym (alaw2 Y))))))))


astrnat : ∀{C D}{J : Fun C D}{M : RMonad J}(alg : RAlg M){X Y}
          (f : Cat.Hom C X Y) → 
          (g : Cat.Hom D (OMap J X) (RAlg.acar alg))
          (g' : Cat.Hom D (OMap J Y) (RAlg.acar alg)) →
          Cat.comp D g' (HMap J f) ≅ g → 
          Cat.comp D (RAlg.astr alg g') 
                     (RMonad.bind M (Cat.comp D (RMonad.η M) (HMap J f))) 
          ≅ 
          RAlg.astr alg g
astrnat {C}{D}{J}{M} alg f g g' p = let 
  open RMonad M; open RAlg alg; open Cat D in
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

record RAlgMorph {C D : Cat}{J : Fun C D}{M : RMonad J}(A B : RAlg M) : Set 
  where
  open Cat D
  open RAlg
  field amor : Hom (acar A) (acar B)
        ahom : ∀{Z}{f : Hom (OMap J Z) (acar A)} → 
               comp amor (astr A f) ≅ astr B (comp amor f)
open RAlgMorph

RAlgMorphEq : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}
              {f g : RAlgMorph X Y} → amor f ≅ amor g → f ≅ g
RAlgMorphEq {C}{D}{J}{M}{X}{Y}{f}{g} p = let open Cat D; open RAlg in funnycong
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

lemZ : ∀{C D}{J : Fun C D}{M : RMonad J}{X X' Y Y' : RAlg M}
       {f : RAlgMorph X Y}{g : RAlgMorph X' Y'} → X ≅ X' → Y ≅ Y' → 
             amor f ≅ amor g → f ≅ g
lemZ refl refl = RAlgMorphEq

IdMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{A : RAlg M} → RAlgMorph A A
IdMorph {C}{D}{J}{M}{A} = let open Cat D; open RAlg A in record {
  amor = iden;
  ahom = λ {Z} {f} → 
    proof 
    comp iden (astr f)
    ≅⟨ idl ⟩ 
    astr f
    ≅⟨ cong astr (sym idl) ⟩ 
    astr (comp iden f) 
    ∎}

CompMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y Z : RAlg M} → 
            RAlgMorph Y Z → RAlgMorph X Y → RAlgMorph X Z
CompMorph {C}{D}{J}{M}{X}{Y}{Z} f g = let open Cat D; open RAlg in record {
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

idlMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}{f : RAlgMorph X Y} →
           CompMorph IdMorph f ≅ f
idlMorph {C}{D} = RAlgMorphEq (Cat.idl D)

idrMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{X Y : RAlg M}{f : RAlgMorph X Y} →
           CompMorph f IdMorph ≅ f
idrMorph {C}{D} = RAlgMorphEq (Cat.idr D) 

assMorph : ∀{C D}{J : Fun C D}{M : RMonad J}{W X Y Z : RAlg M}
           {f : RAlgMorph Y Z}{g : RAlgMorph X Y}{h : RAlgMorph W X} →
           CompMorph (CompMorph f g) h ≅ CompMorph f (CompMorph g h)
assMorph {C}{D} = RAlgMorphEq (Cat.ass D)

EM : ∀{C D}{J : Fun C D} → RMonad J → Cat
EM {C}{D}{J} M = record{
  Obj  = RAlg M;
  Hom  = RAlgMorph;
  iden = IdMorph;
  comp = CompMorph;
  idl  = idlMorph;
  idr  = idrMorph;
  ass  = λ{_}{_}{_}{_}{f}{g}{h} → assMorph {_}{_}{_}{_}{_}{_}{_}{_}{f}{g}{h}}


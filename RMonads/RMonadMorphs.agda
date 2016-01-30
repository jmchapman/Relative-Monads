module RMonads.RMonadMorphs where

open import Library
open import Functors
open import Categories
open import RMonads

open Fun
open RMonad

record RMonadMorph {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
                   (M M' : RMonad J) : Set (a ⊔ b ⊔ c ⊔ d) where
  constructor rmonadmorph
  open Cat D
  field morph    : ∀ {X} → Hom (T M X) (T M' X)
        lawη     : ∀ {X} → comp morph (η M {X}) ≅ η M' {X}
        lawbind : ∀ {X Y}{k : Hom (OMap J X) (T M Y)} → 
                  comp (morph {Y}) (bind M k) 
                  ≅ 
                  comp (bind M' (comp (morph {Y}) k)) (morph {X})


RMonadMorphEq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
  {M M' : RMonad J}(α α' : RMonadMorph M M') ->
  (λ {X} -> RMonadMorph.morph α {X}) ≅ (λ {X} -> RMonadMorph.morph α' {X}) →
  α ≅ α'
RMonadMorphEq (rmonadmorph m lη lbind) (rmonadmorph .m lη' lbind') refl =
  cong₂ (rmonadmorph m)
        (iext λ _ → hir refl)
        (iext λ _ → iext λ _ → iext λ _ → hir refl)

IdRMonadMorph : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
  (M  : RMonad J) → RMonadMorph M M
IdRMonadMorph {D = D} M = rmonadmorph
  iden
  idl
  (trans idl (trans (cong (bind M) (sym idl)) (sym idr)))
  where open Cat D

CompRMonadMorph : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}
  {M  M' M'' : RMonad J} →
  RMonadMorph M' M'' → RMonadMorph M M' → RMonadMorph M M''
CompRMonadMorph {D = D}{M'' = M''}
  (rmonadmorph f lawηf lawbindf)
  (rmonadmorph g lawηg lawbindg) =
  rmonadmorph
    (comp f g)
    (trans ass (trans (cong (comp f) lawηg) lawηf))
    \ {_ _ k} -> trans
      ass
      (trans (cong (comp f) lawbindg)
             (trans (trans (sym ass)
                           (cong (λ f → comp f g)
                                 (trans (lawbindf {k = comp g k})
                                        (cong (λ g → comp (bind M'' g) f)
                                              (sym ass)))))
                     ass))
  where open Cat D

idr : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}{M M' : RMonad J}
  (f : RMonadMorph M M') → CompRMonadMorph f (IdRMonadMorph _) ≅ f
idr {D = D} f = RMonadMorphEq _ _ (iext λ _ → Cat.idr D)

idl : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{J : Fun C D}{M M' : RMonad J}
  (f : RMonadMorph M M') → CompRMonadMorph (IdRMonadMorph _) f ≅ f
idl {D = D} f = RMonadMorphEq _ _ (iext λ _ → Cat.idl D)

ass : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}
  {J : Fun C D}{M M' M'' M''' : RMonad J}
  (f : RMonadMorph M'' M''')(g : RMonadMorph M' M'')(h : RMonadMorph M M')  →
  CompRMonadMorph (CompRMonadMorph f g) h
  ≅
  CompRMonadMorph f (CompRMonadMorph g h)
ass {D = D} f g h = RMonadMorphEq _ _ (iext λ _ → Cat.ass D)


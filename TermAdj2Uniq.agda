{-# OPTIONS --type-in-type #-}
module TermAdj2Uniq where

open import Categories
open import Functors
open import Adjunctions2
open import Monads2
open import EM2
open import CatofAdj2
open import TermAdj2Obj
open import TermAdj2Hom
open import Terminal
open import Relation.Binary.HeterogeneousEquality
open import Equality
open Fun
open Adj
open ObjAdj
open Cat

omaplem : ∀{C}(M : Monad C)(A : ObjAdj M)(V : HomAdj A (EMObj M)) → OMap (HomAdj.K (EMHom M {A})) ≅ OMap (HomAdj.K V)
omaplem {C} M A V = ext
                     (λ X →
                        AlgEq (fcong X (cong OMap (HomAdj.Rlaw V)))
                        (ext
                         (λ Y →
                            dext
                            (λ {f} {f'} p →
                               trans
                               (trans
                                (trans
                                 (stripsubst (λ Z → Hom C Z (OMap (R (adj A)) X))
                                  (HMap (R (adj A)) (right (adj A) f)) (fcong Y (cong OMap (law A))))
                                 (cong' refl (cong
                                                (λ (F : Obj (D A) → Obj C) →
                                                   λ (_ : Hom (D A) (OMap (L (adj A)) Y) X) →
                                                     Hom C (F (OMap (L (adj A)) Y)) (F X))
                                                (cong OMap (HomAdj.Rlaw V)))
                                    (icong' refl
                                     (cong
                                      (λ (F : Obj (D A) → Obj C) →
                                         λ (z : Obj (D A)) →
                                           Hom (D A) (OMap (L (adj A)) Y) z →
                                           Hom C (F (OMap (L (adj A)) Y)) (F z))
                                      (cong OMap (HomAdj.Rlaw V)))
                                     (icong' refl
                                      (cong
                                       (λ (F : Obj (D A) → Obj C) →
                                          λ (z : Obj (D A)) →
                                            {Y₁ : Obj (D A)} → Hom (D A) z Y₁ → Hom C (F z) (F Y₁))
                                       (cong OMap (HomAdj.Rlaw V)))
                                      (cong HMap (HomAdj.Rlaw V)) (refl {x = OMap (L (adj A)) Y}))
                                     (refl {x = X}))
                                    (refl {x = right (adj A) f})))
                                (cong₃ (λ A₁ B → AlgMorph.amor {C} {M} {A₁} {B})
                                 (fcong Y (cong OMap (HomAdj.Llaw V))) refl
                                 (HomAdj.rightlaw V {Y} {X} {f})))
                               (cong (Alg.astr (OMap (HomAdj.K V) X) Y)
                                (trans
                                 (stripsubst (Hom C Y) f (fcong X (cong OMap (HomAdj.Rlaw V))))
                                 p))))))

hmaplem : ∀{C}(M : Monad C)(A : ObjAdj M)(V : HomAdj A (EMObj M)){X Y : Obj (D A)} (f : Hom (D A) X Y) →
          HMap (HomAdj.K (EMHom M {A})) f ≅ HMap (HomAdj.K V) f 
hmaplem {C} M A V {X}{Y} f = lemZ (fcong X (omaplem M A V)) 
                                  (fcong Y (omaplem M A V)) 
                                  (cong' refl (cong
                                                 (λ (F : Obj (D A) → Obj C) →
                                                    λ (_ : Hom (D A) X Y) → Hom C (F X) (F Y))
                                                 (cong OMap (HomAdj.Rlaw V)))
                                     (icong' refl (cong
                                                     (λ (F : Obj (D A) → Obj C) →
                                                        λ (z : Obj (D A)) → Hom (D A) X z → Hom C (F X) (F z))
                                                     (cong OMap (HomAdj.Rlaw V)))
                                      (icong' refl (cong
                                                      (λ (F : Obj (D A) → Obj C) →
                                                         λ (z : Obj (D A)) →
                                                           {Y₁ : Obj (D A)} → Hom (D A) z Y₁ → Hom C (F z) (F Y₁))
                                                      (cong OMap (HomAdj.Rlaw V))) (cong HMap (HomAdj.Rlaw V)) (refl {x = X}))
                                      (refl {x = Y}))
                                     (refl {x = f}))


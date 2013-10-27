{-# OPTIONS --type-in-type #-}
module WellScopedTerms where

open import Function
open import Utilities
open import Categories
open import Functors
open import Nat
open import Sets
open import Fin
open import RMonads2
open import Relation.Binary.HeterogeneousEquality
open import Equality

open Cat
open Fun

data Tm : Nat → Set where
  var : ∀{n} → Fin n → Tm n
  lam : ∀{n} → Tm (s n) → Tm n
  app : ∀{n} → Tm n → Tm n → Tm n

Ren : Nat → Nat → Set
Ren m n = Fin m → Fin n

-- Weakening a renaming (to push it under a lambda)

wk : ∀{m n} → Ren m n → Ren (s m) (s n)
wk f fz     = fz
wk f (fs i) = fs (f i)

-- Performing a renaming on an expression

ren : ∀{m n} → Ren m n → Tm m → Tm n
ren f (var i)   = var (f i)
ren f (app t u) = app (ren f t) (ren f u)
ren f (lam t)   = lam (ren (wk f) t)

-- Identity renaming

renId : ∀{n} → Ren n n
renId = id

-- Composition of renamings

renComp : ∀{m n o} → Ren n o → Ren m n → Ren m o
renComp f g = f ∘ g

-- we prove that wk is an endofunctor

wkid : ∀{n}(i : Fin (s n)) → wk renId i ≅ id i
wkid fz     = refl
wkid (fs i) = refl

wkcomp : ∀{m n o}(f : Ren n o)(g : Ren m n)(i : Fin (s m)) → 
            wk (renComp f g) i ≅ renComp (wk f) (wk g) i
wkcomp f g fz     = refl
wkcomp f g (fs i) = refl

-- we prove that renamings is a functor

renid : ∀{n}(t : Tm n) → ren renId t ≅ t
renid (var i)   = refl
renid (app t u) = cong₂ app (renid t) (renid u)
renid (lam t)   = cong lam (trans (cong (λ f → ren f t) (ext wkid)) 
                                  (renid t))

rencomp : ∀{m n o}(f : Ren n o)(g : Ren m n)(t : Tm m) → 
          ren (renComp f g) t ≅ ren f (ren g t)
rencomp f g (var i)   = refl
rencomp f g (app t u) = cong₂ app (rencomp f g t) (rencomp f g u)
rencomp f g (lam t)   = cong lam (trans (cong (λ f → ren f t) 
                                              (ext (wkcomp f g))) 
                                        (rencomp (wk f) (wk g) t))

-- Substitutions

Sub : Nat → Nat → Set
Sub m n = Fin m → Tm n

-- Weaken a substitution to push it under a lambda

lift : ∀{m n} → Sub m n → Sub (s m) (s n)
lift f fz     = var fz
lift f (fs i) = ren fs (f i)

-- Perform substitution on an expression

sub : ∀{m n} → Sub m n → Tm m → Tm n
sub f (var i)   = f i
sub f (app t u) = app (sub f t) (sub f u)
sub f (lam t)   = lam (sub (lift f) t)

-- Identity substitution

subId : ∀{n} → Sub n n
subId = var

-- Composition of substitutions 

subComp : ∀{m n o} → Sub n o → Sub m n → Sub m o
subComp f g = sub f ∘ g

-- lift is an endofunctor on substitutions and sub is a functor, we
-- need some auxilary lemmas for the composition cases

-- the conditions for identity are easy

liftid : ∀{n}(i : Fin (s n)) → lift subId i ≅ subId i
liftid fz     = refl
liftid (fs i) = refl

subid : ∀{n}(t : Tm n) → sub subId t ≅ id t
subid (var i)   = refl
subid (app t u) = cong₂ app (subid t) (subid u)
subid (lam t)   = cong lam (trans (cong (λ f → sub f t) (ext liftid)) 
                                  (subid t))  

-- for composition of subs (subcomp) and lifts (liftcomp) we need two
-- lemmas about how renaming and subs interact for these two lemmas we
-- need two lemmas about how lift and wk interact.

liftwk : ∀{m n o}(f : Sub n o)(g : Ren m n)(i : Fin (s m)) → 
            (lift f ∘ wk g) i ≅ lift (f ∘ g) i
liftwk f g fz     = refl
liftwk f g (fs i) = refl

subren : ∀{m n o}(f : Sub n o)(g : Ren m n)(t : Tm m) → 
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g (var i)   = refl
subren f g (app t u) = cong₂ app (subren f g t) (subren f g u)
subren f g (lam t)   = cong lam (trans (subren (lift f) (wk g) t)
                                       (cong (λ f → sub f t) 
                                             (ext (liftwk f g))))

renwklift : ∀{m n o}(f : Ren n o)(g : Sub m n)(i : Fin (s m)) → 
               (ren (wk f) ∘ lift g) i ≅ lift (ren f ∘ g) i
renwklift f g fz     = refl
renwklift f g (fs i) = trans (sym (rencomp (wk f) fs (g i))) 
                                (rencomp fs f (g i))

rensub : ∀{m n o}(f : Ren n o)(g : Sub m n)(t : Tm m) →
         (ren f ∘ sub g) t ≅ sub (ren f ∘ g) t
rensub f g (var i)   = refl
rensub f g (app t u) = cong₂ app (rensub f g t) (rensub f g u)
rensub f g (lam t)   = cong lam (trans (rensub (wk f) (lift g) t)
                                       (cong (λ f → sub f t) 
                                             (ext (renwklift f g))))

liftcomp : ∀{m n o}(f : Sub n o)(g : Sub m n)(i : Fin (s m)) → 
           lift (subComp f g) i ≅ subComp (lift f) (lift g) i
liftcomp f g fz     = refl
liftcomp f g (fs i) = trans (rensub fs f (g i))
                           (sym (subren (lift f) fs (g i)))

subcomp : ∀{m n o}(f : Sub n o)(g : Sub m n)(t : Tm m) → 
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g (var i)   = refl
subcomp f g (app t u) = cong₂ app (subcomp f g t) (subcomp f g u)
subcomp f g (lam t)   = cong lam (trans (cong (λ f → sub f t) 
                                              (ext (liftcomp f g))) 
                                        (subcomp (lift f) (lift g) t))

TmRMonad : RMonad FinF
TmRMonad = record {
  T    = Tm; 
  η    = var;
  _* = sub; 
  law1 = ext subid; 
  law2 = refl;
  law3 = ext (subcomp _ _)}

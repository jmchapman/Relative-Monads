{-# OPTIONS --type-in-type #-}
module WellScopedTerms where

open import Function
open import Categories
open import Functors
open import Sets
open import Fin
open import RMonads2
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Equality
open import Data.Nat
open import Data.Fin hiding (lift)
open Cat
open Fun

data Tm : ℕ → Set where
  var : ∀{n} → Fin n → Tm n
  lam : ∀{n} → Tm (suc n) → Tm n
  app : ∀{n} → Tm n → Tm n → Tm n

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

-- Weakening a renaming (to push it under a lambda)

wk : ∀{m n} → Ren m n → Ren (suc m) (suc n)
wk f zero     = zero
wk f (suc i) = suc (f i)

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

wkid : ∀{n}(i : Fin (suc n)) → wk renId i ≅ id i
wkid zero    = refl
wkid (suc i) = refl

wkcomp : ∀{m n o}(f : Ren n o)(g : Ren m n)(i : Fin (suc m)) → 
            wk (renComp f g) i ≅ renComp (wk f) (wk g) i
wkcomp f g zero    = refl
wkcomp f g (suc i) = refl

-- we prove that renamings is a functor

renid : ∀{n}(t : Tm n) → ren renId t ≅ t
renid (var i)   = refl
renid (app t u) = cong₂ app (renid t) (renid u)
renid (lam t)   = 
  proof 
  lam (ren (wk renId) t) 
  ≅⟨ cong (λ f → lam (ren f t)) (ext wkid) ⟩ 
  lam (ren renId t) 
  ≅⟨ cong lam (renid t) ⟩ 
  lam t 
  ∎

rencomp : ∀{m n o}(f : Ren n o)(g : Ren m n)(t : Tm m) → 
          ren (renComp f g) t ≅ ren f (ren g t)
rencomp f g (var i)   = refl
rencomp f g (app t u) = cong₂ app (rencomp f g t) (rencomp f g u)
rencomp f g (lam t)   = 
  proof 
  lam (ren (wk (renComp f g)) t)  
  ≅⟨ cong (λ f → lam (ren f t)) (ext (wkcomp f g)) ⟩ 
  lam (ren (renComp (wk f) (wk g)) t)  
  ≅⟨ cong lam (rencomp (wk f) (wk g) t) ⟩ 
  lam (ren (wk f) (ren (wk g) t))
  ∎

-- Substitutions

Sub : ℕ → ℕ → Set
Sub m n = Fin m → Tm n

-- Weaken a substitution to push it under a lambda

lift : ∀{m n} → Sub m n → Sub (suc m) (suc n)
lift f zero     = var zero
lift f (suc i) = ren suc (f i)

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

liftid : ∀{n}(i : Fin (suc n)) → lift subId i ≅ subId i
liftid zero    = refl
liftid (suc i) = refl

subid : ∀{n}(t : Tm n) → sub subId t ≅ id t
subid (var i)   = refl
subid (app t u) = 
  proof 
  app (sub subId t) (sub subId u) 
  ≅⟨ cong₂ app (subid t) (subid u) ⟩ 
  app t u 
  ∎
subid (lam t)   = 
  proof 
  lam (sub (lift subId) t) 
  ≅⟨ cong lam (cong (λ f → sub f t) (ext liftid)) ⟩ 
  lam (sub subId t) 
  ≅⟨ cong lam (subid t) ⟩ 
  lam t 
  ∎

-- for composition of subs (subcomp) and lifts (liftcomp) we need two
-- lemmas about how renaming and subs interact for these two lemmas we
-- need two lemmas about how lift and wk interact.

liftwk : ∀{m n o}(f : Sub n o)(g : Ren m n)(i : Fin (suc m)) → 
            (lift f ∘ wk g) i ≅ lift (f ∘ g) i
liftwk f g zero    = refl
liftwk f g (suc i) = refl

subren : ∀{m n o}(f : Sub n o)(g : Ren m n)(t : Tm m) → 
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g (var i)   = refl
subren f g (app t u) = 
  proof
  app (sub f (ren g t)) (sub f (ren g u))
  ≅⟨ cong₂ app (subren f g t) (subren f g u) ⟩
  app (sub (f ∘ g) t) (sub (f ∘ g) u) 
  ∎
subren f g (lam t)   = 
  proof
  lam (sub (lift f) (ren (wk g) t))
  ≅⟨ cong lam (subren (lift f) (wk g) t) ⟩
  lam (sub (lift f ∘ wk g) t)
  ≅⟨ cong lam (cong (λ f₁ → sub f₁ t) (ext (liftwk f g))) ⟩
  lam (sub (lift (f ∘ g)) t) 
  ∎ 

renwklift : ∀{m n o}(f : Ren n o)(g : Sub m n)(i : Fin (suc m)) → 
               (ren (wk f) ∘ lift g) i ≅ lift (ren f ∘ g) i
renwklift f g zero    = refl
renwklift f g (suc i) = 
  proof
  ren (wk f) (ren suc (g i))
  ≅⟨ sym (rencomp (wk f) suc (g i)) ⟩
  ren (wk f ∘ suc) (g i)
  ≡⟨⟩
  ren (suc ∘ f) (g i)
  ≅⟨ rencomp suc f (g i) ⟩
  ren suc (ren f (g i))
  ∎

rensub : ∀{m n o}(f : Ren n o)(g : Sub m n)(t : Tm m) →
         (ren f ∘ sub g) t ≅ sub (ren f ∘ g) t
rensub f g (var i)   = refl
rensub f g (app t u) = 
  proof
  app (ren f (sub g t)) (ren f (sub g u))
  ≅⟨ cong₂ app (rensub f g t) (rensub f g u) ⟩
  app (sub (ren f ∘ g) t) (sub (ren f ∘ g) u)
  ∎
rensub f g (lam t)   = 
  proof
  lam (ren (wk f) (sub (lift g) t))
  ≅⟨ cong lam (rensub (wk f) (lift g) t) ⟩
  lam (sub (ren (wk f) ∘ (lift g)) t)
  ≅⟨ cong (λ f → lam (sub f t)) (ext (renwklift f g)) ⟩
  lam (sub (lift (ren f ∘ g)) t) 
  ∎ 

liftcomp : ∀{m n o}(f : Sub n o)(g : Sub m n)(i : Fin (suc m)) → 
           lift (subComp f g) i ≅ subComp (lift f) (lift g) i
liftcomp f g zero    = refl
liftcomp f g (suc i) = 
  proof
  ren suc (sub f (g i))
  ≅⟨ rensub suc f (g i) ⟩
  sub (ren suc ∘ f) (g i)
  ≅⟨ sym (subren (lift f) suc (g i)) ⟩
  sub (lift f) (ren suc (g i))
  ∎ 

subcomp : ∀{m n o}(f : Sub n o)(g : Sub m n)(t : Tm m) → 
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g (var i)   = refl
subcomp f g (app t u) = 
  proof
  app (sub (subComp f g) t) (sub (subComp f g) u) 
  ≅⟨ cong₂ app (subcomp f g t) (subcomp f g u) ⟩
  app (sub f (sub g t)) (sub f (sub g u))
  ∎ 
subcomp f g (lam t)   = 
  proof
  lam (sub (lift (subComp f g)) t) 
  ≅⟨ cong (λ f → lam (sub f t)) (ext (liftcomp f g)) ⟩
  lam (sub (subComp (lift f)(lift g)) t)
  ≅⟨ cong lam (subcomp (lift f) (lift g) t) ⟩
  lam (sub (lift f) (sub (lift g) t))
  ∎

TmRMonad : RMonad FinF
TmRMonad = record {
  T    = Tm; 
  η    = var;
  bind = sub; 
  law1 = ext subid; 
  law2 = refl;
  law3 = ext (subcomp _ _)}

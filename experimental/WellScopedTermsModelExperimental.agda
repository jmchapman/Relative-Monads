{-# OPTIONS --type-in-type --copatterns #-}

module experimental.WellScopedTermsModelExperimental where

open import Library
open import WellScopedTerms
open import RMonads
open import RMonads.REM
open import Categories.Sets

-- some experiments
open import experimental.Delay
open import Size

mutual
  Env : ℕ → Set
  Env n = Fin n → Val

  data Val : Set where
    clo : ∀{n} → Env n → Tm (suc n) → Val

{-
mutual
  _$$_ : Val → Val → Val
  clo γ t $$ v = ev (γ << v) t

  ev : ∀{n} → Env n → Tm n → Val
  ev γ (var x) = γ x
  ev γ (lam t) = clo γ t
  ev γ (app t u) = ev γ t $$ ev γ u
-}

-- the RAlg is expecting a env containing 'values' here the values
-- evaluator takes an env of undelayed values and makes a delayed
-- values.
mutual
  ev : ∀{i n} → Env n → Tm n → Delay Val i
  ev γ (var x) = now (γ x)
  ev γ (lam t) = now (clo γ t)
  ev γ (app t u) = ev γ t >>= λ f → ev γ u >>= λ v → f $$ v

  _∞$$_ : ∀{i} → Val → Val → ∞Delay Val i
  force (clo γ t ∞$$ v) = ev (γ << v) t 

  _$$_ : ∀{i} → Val → Val → Delay Val i
  f $$ v = later (f ∞$$ v)

{-
mutual
  Env' : ∀ i → ℕ → Set
  Env' i n = Fin n → Delay (Val' i) i

  data Val' (i : Size) :  Set where
    clo : ∀{n} → Env' i n → Tm (suc n) → Val' i

mutual
  ev' : ∀{i n} → Env' i n → Tm n → Delay (Val' i) i
  ev' γ (var x)   = γ x
  ev' γ (lam t)   = now (clo γ t)
  ev' γ (app t u) = {!!}

  _∞$$'_ : ∀{i} → Val' i → Delay (Val' i) i → ∞Delay (Val' i) i
  force (clo γ t ∞$$' v) = ev' (γ << v) t 
-}

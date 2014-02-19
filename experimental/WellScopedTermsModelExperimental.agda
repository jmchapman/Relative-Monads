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

module EnvVal where
  mutual
    Env : ℕ → Set
    Env n = Fin n → Val
  
    data Val : Set where
      clo : ∀{n} → Env n → Tm (suc n) → Val
  
  _<<_ : ∀{n} → Env n → Val → Env (suc n)
  (γ << v) zero    = v
  (γ << v) (suc n) = γ n
  
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
    ev : ∀{i n} → Env n → Tm n → Delay i Val
    ev γ (var x) = now (γ x)
    ev γ (lam t) = now (clo γ t)
    ev γ (app t u) = ev γ t >>= λ f → ev γ u >>= λ v → f $$ v
  
    _∞$$_ : ∀{i} → Val → Val → ∞Delay i Val
    force (clo γ t ∞$$ v) = ev (γ << v) t 
  
    _$$_ : ∀{i} → Val → Val → Delay i Val
    f $$ v = later (f ∞$$ v)
  

module EnvDelayVal where
mutual
  Env : ℕ → Set
  Env n = Fin n → ∀{i} → Delay i Val

  data Val :  Set where
    clo : ∀{n} → Env n → Tm (suc n) → Val

  _<<_ : ∀{n} → Env n → Val → Env (suc n)
  (γ << v) zero    = now v
  (γ << v) (suc n) = γ n


mutual
  ev : ∀{i n} → Env n → Tm n → Delay i Val
  ev γ (var x)   = γ x
  ev γ (lam t)   = now (clo γ t)
  ev γ (app t u) = ev γ t >>= (λ f → ev γ u >>= (λ v → f $$ v))

  _∞$$_ : ∀ {i} → Val → Val → ∞Delay i Val
  force (clo γ t ∞$$ v) = ev (γ << v) t

  _$$_ : ∀{i} → Val → Val → Delay i Val
  f $$ v = later (f ∞$$ v)



TmRAlg : RAlg TmRMonad
TmRAlg  = record{
  acar  = ∀ {i} → Delay i Val; --S;
  astr  = λ γ t → ev γ t;
  alaw1 = refl; --ext λ _ → sym lawvar;
  alaw2 = {!!}} -- ext λ t → subeval t _ _}       

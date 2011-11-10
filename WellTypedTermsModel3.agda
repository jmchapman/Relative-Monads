{-# OPTIONS --type-in-type #-}
module WellTypedTermsModel3 where

open import Utilities
open import Naturals
open import WellTypedTerms3
open import REM2
open import FunctorCat
open import Sets
open import Equality

open NatT

-- interpretation of types

Val : Ty → Set
Val ι       = One
Val (σ ⇒ τ) = Val σ → Val τ

-- interpretation of contexts

Env : Con → Set
Env Γ = ∀{σ} →  Var Γ σ → Val σ

_<<_ : ∀{Γ σ} → Env Γ → Val σ → Env (Γ < σ)
(γ << v) vz     = v
(γ << v) (vs x) = γ x

-- intepretation of terms

eval : ∀{Γ σ} → Env Γ → Tm Γ σ → Val σ
eval γ (var x)   = γ x
eval γ (app t u) = eval γ t (eval γ u)
eval γ (lam t)   = λ v → eval (γ << v) t

substeval : ∀{σ τ}(p : σ ≅ τ){Γ : Con}{γ : Env Γ}(t : Tm Γ σ) → 
      (subst Val p  • eval γ) t ≅ (eval γ • subst (Tm Γ) p) t
substeval refl t = refl

wk<< : ∀{Γ Δ}(α  : Ren Γ Δ)(β : Env Δ){σ}(v : Val σ) →
          ∀{ρ}(y : Var (Γ < σ) ρ) → 
          ((β • α) << v) y ≅ (β << v) (wk α y)
wk<< α β v vz     = refl
wk<< α β v (vs y) = refl

reneval : ∀{Γ Δ σ}(α : Ren Γ Δ)(β : Env Δ)(t : Tm Γ σ) →
          eval (eval β • (var • α)) t
          ≅ 
          (eval β • ren α) t
reneval α β (var x) = refl
reneval α β (app t u) = resp2 (λ f x → f x) (reneval α β t) (reneval α β u) 
reneval α β (lam t) = ext λ v → 
  trans (resp (λ (γ : Env _) → eval γ t) (iext λ ρ → ext (wk<< α β v))) 
        (reneval (wk α) (β << v) t)

lifteval : ∀{Γ Δ σ τ}(α : Sub Γ Δ)(β : Env Δ)(v : Val σ)(y : Var (Γ < σ) τ) →
            ((eval β • α) << v) y ≅ (eval (β << v) • lift α) y
lifteval α β v vz     = refl
lifteval α β v (vs x) = reneval vs (β << v) (α x)

subeval : ∀{Γ Δ σ}(α : Sub Γ Δ)(β : Env Δ)(t : Tm Γ σ) → 
          eval (eval β • α) t ≅ (eval β • sub α) t
subeval α β (var x)   = refl
subeval α β (app t u) = resp2 (λ f x → f x) (subeval α β t) (subeval α β u)
subeval α β (lam t)   = 
  ext λ v → trans (resp (λ (γ : Env _) → eval γ t)
                        (iext λ τ → ext (lifteval α β v))) 
                  (subeval (lift α) (β << v) t)

modelRAlg : RAlg TmRMonad
modelRAlg = record {
  acar  = Val; 
  astr  = λ {Γ} → λ γ → eval γ; 
  alaw1 = refl; 
  alaw2 = λ {Γ Δ α γ} → iext λ σ → ext (subeval α γ)}

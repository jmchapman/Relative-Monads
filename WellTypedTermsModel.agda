module WellTypedTermsModel where

open import Library
open import WellTypedTerms
open import RMonads.REM
open import FunctorCat
open import Categories.Sets


-- interpretation of types

Val : Ty → Set
Val ι       = ⊤
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
      (subst Val p  ∘ eval γ) t ≅ (eval γ ∘ subst (Tm Γ) p) t
substeval refl t = refl

wk<< : ∀{Γ Δ}(α  : Ren Γ Δ)(β : Env Δ){σ}(v : Val σ) →
          ∀{ρ}(y : Var (Γ < σ) ρ) → 
          ((β ∘ α) << v) y ≅ (β << v) (wk α y)
wk<< α β v vz     = refl
wk<< α β v (vs y) = refl

reneval : ∀{Γ Δ σ}(α : Ren Γ Δ)(β : Env Δ)(t : Tm Γ σ) →
          eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β (var x)   = refl
reneval α β (app t u) = 
  proof 
  eval (β ∘ α) t (eval (β ∘ α) u)
  ≅⟨ cong₂ (λ f x → f x) (reneval α β t) (reneval α β u) ⟩
  eval β (ren α t) (eval β (ren α u))
  ∎
reneval α β (lam t)   = ext λ v → 
  proof 
  eval ((β ∘ α) << v) t
  ≅⟨ cong (λ (γ : Env _) → eval γ t) (iext λ _ → ext (wk<< α β v)) ⟩ 
  eval (β << v ∘ wk α) t
  ≅⟨ reneval (wk α) (β << v) t ⟩ 
  eval (β << v) (ren (wk α) t)
  ∎

lifteval : ∀{Γ Δ σ τ}(α : Sub Γ Δ)(β : Env Δ)(v : Val σ)(y : Var (Γ < σ) τ) →
            ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v vz     = refl
lifteval α β v (vs x) = 
  proof 
  eval β (α x) 
  ≅⟨ reneval vs (β << v) (α x) ⟩ 
  eval (β << v) (ren vs (α x)) 
  ∎

subeval : ∀{Γ Δ σ}(α : Sub Γ Δ)(β : Env Δ)(t : Tm Γ σ) → 
          eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β (var x)   = refl
subeval α β (app t u) = 
  proof 
  eval (eval β ∘ α) t (eval (eval β ∘ α) u)
  ≅⟨ cong₂ (λ f x → f x) (subeval α β t) (subeval α β u) ⟩
  eval β (sub α t) (eval β (sub α u))
  ∎
subeval α β (lam t)   = ext λ v → 
  proof
  eval ((eval β ∘ α) << v) t 
  ≅⟨ cong (λ (γ : Env _) → eval γ t) (iext λ _ → ext (lifteval α β v)) ⟩
  eval (eval (β << v) ∘ lift α) t
  ≅⟨ subeval (lift α) (β << v) t ⟩
  eval (β << v) (sub (lift α) t) 
  ∎ 

modelRAlg : RAlg TmRMonad
modelRAlg = record {
  acar  = Val; 
  astr  = λ {Γ} → λ γ → eval γ; 
  alaw1 = refl; 
  alaw2 = λ {Γ Δ α γ} → iext λ σ → ext (subeval α γ)}

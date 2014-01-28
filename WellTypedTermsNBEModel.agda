{-# OPTIONS --type-in-type #-}
module WellTypedTermsNBEModel where

open import Naturals
open import WellTypedTerms
open import RMonads.REM
open import FunctorCat
open import Categories.Sets
open import Equality
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Function
open NatT
open Σ

-- normal forms

mutual
  data Nf (Γ : Con) : Ty → Set where
    lam : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne  : Ne Γ ι → Nf Γ ι

  data Ne (Γ : Con) : Ty → Set where
    var : ∀{σ} → Var Γ σ → Ne Γ σ
    app : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ

mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf ρ (lam n) = lam (renNf (wk ρ) n)
  renNf ρ (ne n)  = ne  (renNe ρ n)

  renNe : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe ρ (var x)    = var (ρ x)
  renNe ρ (app n n') = app (renNe ρ n) (renNf ρ n')

mutual
  renNfid : ∀{Γ} σ (v : Nf Γ σ) → renNf id v ≅ v
  renNfid ι (ne x) = cong ne (renNeid ι x)
  renNfid (σ ⇒ τ) (lam v) = cong lam $
    proof 
    renNf (wk id) v 
    ≅⟨ cong (λ (ρ : Ren _ _) → renNf ρ v)
            (iext λ _ → ext wkid) ⟩ 
    renNf id v 
    ≅⟨ renNfid τ v ⟩ 
    v 
    ∎

  renNeid : ∀{Γ} σ (v : Ne Γ σ) → renNe id v ≅ v
  renNeid σ (var x) = refl
  renNeid τ (app {σ} v x) = cong₂ app (renNeid (σ ⇒ τ) v) (renNfid σ x)

mutual
  renNecomp : ∀{Δ Γ B}(ρ : Ren Δ Γ)(ρ' : Ren Γ B) σ (v : Ne Δ σ) → 
             renNe (ρ' ∘ ρ) v ≅ renNe ρ' (renNe ρ v)
  renNecomp ρ ρ' σ (var x)       = refl
  renNecomp ρ ρ' τ (app {σ} v x) = cong₂ 
    Ne.app 
    (renNecomp ρ ρ' (σ ⇒ τ) v) 
    (renNfcomp ρ ρ' σ x)

  renNfcomp : ∀{Δ Γ B}(ρ : Ren Δ Γ)(ρ' : Ren Γ B) σ (v : Nf Δ σ) → 
             renNf (ρ' ∘ ρ) v ≅ renNf ρ' (renNf ρ v)
  renNfcomp ρ ρ' (σ ⇒ τ) (lam v) = cong Nf.lam $
    proof
    renNf (wk (ρ' ∘ ρ)) v 
    ≅⟨ cong (λ (ρ : Ren _ _) → renNf ρ v)
            (iext λ _ → ext (wkcomp ρ' ρ)) ⟩ 
    renNf (wk ρ' ∘ wk ρ) v 
    ≅⟨ renNfcomp (wk ρ) (wk ρ') τ v ⟩ 
    renNf (wk ρ') (renNf (wk ρ) v) 
    ∎
  renNfcomp ρ ρ' ι       (ne x)  = cong ne (renNecomp ρ ρ' ι x)
-- interpretation of types

mutual
  Val : Con → Ty → Set
  Val Γ ι       = Ne Γ ι
  Val Γ (σ ⇒ τ) = ∀{B} →  Ren Γ B → Val B σ → Val B τ

--      (λ f → ∀{B B'}(ρ : Ren Γ B)(ρ' : Ren B B')(a : Val B σ) → renV ρ' (f ρ a) ≅ f (ρ' ∘ ρ) (renV ρ' a))

renV : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Val Δ σ → Val Γ σ
renV ρ {ι}     n = renNe ρ n
renV {Γ}{Δ} ρ {σ ⇒ τ} f = λ ρ' → f (ρ' ∘ ρ)


{-
Ren Γ B → Val B σ → Val B τ 
|                       |
\/                      \/
Ren Γ B' → Val B' σ → Val B' τ


-}
-- interpretation of contexts

Env : Con → Con → Set
Env Γ Δ = ∀{σ} →  Var Γ σ → Val Δ σ

_<<_ : ∀{Γ Δ σ} → Env Γ Δ → Val Δ σ → Env (Γ < σ) Δ
(γ << v) vz     = v
(γ << v) (vs x) = γ x

eval : ∀{Γ Δ σ} → Env Δ Γ → Tm Δ σ → Val Γ σ
eval γ (var i)   = γ i
eval γ (lam t)   = λ ρ v → eval ((renV ρ ∘ γ) << v) t
eval γ (app t u) = eval γ t id (eval γ u)


{-
  lem : ∀{B Γ Δ σ}(ρ : Ren Γ B)(γ : Env Δ Γ)(t : Tm Δ σ) → renV ρ (eval γ t) ≅ eval (renV ρ • γ) t
  lem ρ γ (var x)   = refl
  lem ρ γ (app t u) = trans (snd (eval γ t) id ρ (eval γ u)) 
                            (resp2 (λ f x → f x)
                                   (fresp (λ {_} → id) 
                                          (ifresp _ 
                                                  (resp fst (lem ρ γ t)))) 
                                   (lem ρ γ u))
  lem ρ γ (lam t)   = 
    funeq (λ {B} → ext (λ (ρ' : Ren _ _) → ext (λ v → resp (λ (β : Env _ _) → eval (β << v) t) 
                                               (iext (λ σ → ext (λ a → renVcomp ρ ρ' σ (γ a)))))))
-}

renVid : ∀{Γ} σ (v : Val Γ σ) → renV id v ≅ v
renVid ι       v = renNeid ι v
renVid (σ ⇒ τ) v = refl

renVcomp : ∀{Δ Γ B}(ρ : Ren Δ Γ)(ρ' : Ren Γ B) σ (v : Val Δ σ) → 
         renV (ρ' ∘ ρ) v ≅ renV ρ' (renV ρ v)
renVcomp ρ ρ' ι       v = renNecomp ρ ρ' ι v
renVcomp ρ ρ' (σ ⇒ τ) v = refl


renV<< : ∀{B' B Γ}(α  : Ren B B')(β : Env Γ B){σ}(v : Val B σ) →
        ∀{ρ}(y : Var (Γ < σ) ρ) → 
        ((renV α ∘ β) << renV α v) y ≅ (renV α ∘ (β << v)) y
renV<< α β v vz = refl
renV<< α β v (vs y) = refl

{-

substeval : ∀{σ τ}(p : σ ≅ τ){Γ B : Con}{γ : Env Γ B}(t : Tm Γ σ) → 
      (subst (Val B) p  • eval γ) t ≅ (eval γ • subst (Tm Γ) p) t
substeval refl t = refl

wk<< : ∀{B Γ Δ}(α  : Ren Γ Δ)(β : Env Δ B){σ}(v : Val B σ) →
        ∀{ρ}(y : Var (Γ < σ) ρ) → 
        ((β • α) << v) y ≅ (β << v) (wk α y)
wk<< α β v vz     = refl
wk<< α β v (vs y) = refl

<<eq : ∀{Γ Δ σ}{β β' : Env Γ Δ} → (λ{σ} → β {σ}) ≅ (λ{σ} → β' {σ}) → 
        (v : Val Δ σ) → (λ {σ} → (β << v) {σ}) ≅ (λ {σ} → (β' << v) {σ})
<<eq refl v = refl



reneval : ∀{B Γ Δ σ}(α : Ren Γ Δ)(β : Env Δ B)(t : Tm Γ σ) →
          eval (eval β • (var • α)) t
          ≅ 
          (eval β • ren α) t
reneval α β (var x)   = refl
reneval α β (app t u) = 
  resp2 (λ f x → (fst f) id x) (reneval α β t) (reneval α β u)
reneval {B} α β (lam t) = 
  funeq (λ {B'} → ext (λ (ρ : Ren B B') → ext (λ (v : Val B' _) → 
    trans (resp (λ (γ : Env _ B') → eval γ t) 
                (iext (λ σ' → ext (wk<< α (renV ρ • β) v)))) 
          (reneval (wk α) ((renV ρ • β) << v) t)))) 

lifteval : ∀{B Γ Δ σ τ}(α : Sub Γ Δ)(β : Env Δ B)
           (v : Val B σ)(y : Var (Γ < σ) τ) →
           ((eval β • α) << v) y ≅ (eval (β << v) • lift α) y
lifteval α β v vz     = refl
lifteval α β v (vs x) = reneval vs (β << v) (α x)


subeval : ∀{B Γ Δ σ}(α : Sub Γ Δ)(β : Env Δ B)(t : Tm Γ σ) → 
          eval (eval β • α) t ≅ (eval β • sub α) t
subeval α β (var x)   = refl
subeval α β (app t u) = resp2 (λ f x → (fst f) id x) (subeval α β t) (subeval α β u) 
subeval {B} α β (lam t) = funeq (λ {B'} → ext (λ (ρ : Ren B B') → ext (λ (v : Val B' _) →
  trans (resp (λ (γ : Env _ B') → eval γ t)
              (iext (λ σ' → ext (λ x → trans
                (resp (λ (γ : Env _ B') → (γ << v) x)
                      (iext (λ σ'' → ext (λ a → lem ρ β (α a)))))
                (lifteval α (renV ρ • β) v x)))))
        (subeval (lift α) ((renV ρ • β) << v) t))))

modelRAlg : Con → RAlg TmRMonad
modelRAlg Γ = record {
  acar  = Val Γ;
  astr  = λ γ → eval γ;
  alaw1 = refl;
  alaw2 = λ {B} {Δ} {α} {γ} → iext (λ σ → ext (subeval α γ))} 
-}


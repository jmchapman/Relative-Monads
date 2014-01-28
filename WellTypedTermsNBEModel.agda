{-# OPTIONS --type-in-type #-}
module WellTypedTermsNBEModel where

open import Naturals
open import WellTypedTerms
open import RMonads.REM
open import FunctorCat
open import Categories.Sets
open import Equality
open import Relation.Binary.HeterogeneousEquality
open import Data.Product
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
  renNf ρ (ne n)  = ne  (renN ρ n)

  renN : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Ne Δ σ → Ne Γ σ
  renN ρ (var x) = var (ρ x)
  renN ρ (app n n') = app (renN ρ n) (renNf ρ n')

mutual
  renNfid : ∀{Γ} σ (v : Nf Γ σ) → renNf id v ≅ v
  renNfid ι (ne x) = cong ne (renNid ι x)
  renNfid (σ ⇒ τ) (lam v) = cong lam 
    (trans (cong (λ (ρ : Ren _ _) → renNf ρ v)
                 (iext (λ σ₁ → ext (λ x → wkid x)))) 
           (renNfid τ v))

  renNid : ∀{Γ} σ (v : Ne Γ σ) → renN id v ≅ v
  renNid σ (var x) = refl
  renNid τ (app {σ} v x) = cong₂ app (renNid (σ ⇒ τ) v) (renNfid σ x)

mutual
  renNcomp : ∀{Δ Γ B}(ρ : Ren Δ Γ)(ρ' : Ren Γ B) σ (v : Ne Δ σ) → 
             renN (ρ' ∘ ρ) v ≅ renN ρ' (renN ρ v)
  renNcomp ρ ρ' σ (var x)       = refl
  renNcomp ρ ρ' τ (app {σ} v x) = cong₂ 
    Ne.app 
    (renNcomp ρ ρ' (σ ⇒ τ) v) 
    (renNfcomp ρ ρ' σ x)

  renNfcomp : ∀{Δ Γ B}(ρ : Ren Δ Γ)(ρ' : Ren Γ B) σ (v : Nf Δ σ) → 
             renNf (ρ' ∘ ρ) v ≅ renNf ρ' (renNf ρ v)
  renNfcomp ρ ρ' (σ ⇒ τ) (lam v) = cong 
    Nf.lam 
    (trans (cong (λ (ρ₁ : Ren _ _) → renNf ρ₁ v) (iext (λ σ₁ → ext (λ a → wkcomp ρ' ρ a)))) 
           (renNfcomp (wk ρ) (wk ρ') τ v))
  renNfcomp ρ ρ' ι       (ne x)  = cong ne (renNcomp ρ ρ' ι x)
-- interpretation of types

mutual
  Val : Con → Ty → Set
  Val Γ ι       = Ne Γ ι
  Val Γ (σ ⇒ τ) = 
    Σ (∀{B} →  Ren Γ B → Val B σ → Val B τ) 
      (λ f → ∀{B B'}(ρ : Ren Γ B)(ρ' : Ren B B')(a : Val B σ) → renV ρ' (f ρ a) ≅ f (ρ' ∘ ρ) (renV ρ' a))

  renV : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Val Δ σ → Val Γ σ
  renV ρ {ι}     n = renN ρ n
  renV {Γ}{Δ} ρ {σ ⇒ τ} f = (λ ρ' → proj₁ f (ρ' ∘ ρ)) , (λ ρ' → proj₂ f (ρ' ∘ ρ))

{-
funeq : ∀{Γ σ τ} {f g : Σ (∀{B} →  Ren Γ B → Val B σ → Val B τ)
                      (λ f → ∀{B B'}(ρ : Ren Γ B)(ρ' : Ren B B')(a : Val B σ) → renV ρ' (f ρ a) ≅ f (ρ' ∘ ρ) (renV ρ' a))} →
                 (∀{B} → proj₁ f {B} ≅ proj₁ g {B}) → f ≅ g
funeq {Γ}{σ}{τ}{f}{g} p = funnyresp 
  (iext (λ B → p {B})) 
  (iext (λ B → iext (λ B' → ext (λ (ρ : Ren _ _) → ext (λ (ρ' : Ren _ _) → ext (λ a → fixtypes 
    (resp (renV ρ') (fresp a (fresp (λ {B₁} → ρ {B₁}) (p {B}))))
    (fresp (renV ρ' a) (fresp (λ {_} → ρ' • ρ) (p {B'})))))))))
  _,_



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

mutual
-- intepretation of terms
  eval : ∀{Γ Δ σ} → Env Δ Γ → Tm Δ σ → Val Γ σ
  eval γ (var i)   = γ i
  eval γ (lam t)   = (λ ρ v → eval ((renV ρ • γ) << v) t) , 
   (λ ρ ρ' a → trans (lem ρ' ((renV ρ • γ) << a) t) 
                     (resp (λ (γ₁ : Env _ _) → eval γ₁ t) 
                           (iext (λ _ → ext (λ x → trans (sym (renV<< ρ' (renV ρ • γ) a x)) 
                                                         (resp (λ (γ₁ : Env _ _) → (γ₁ << renV ρ' a) x) 
                                                               (iext (λ _ → ext (λ a' → sym (renVcomp ρ ρ' _ (γ a')))))))))))
  eval γ (app t u) = fst (eval γ t) id (eval γ u)

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


  renVid : ∀{Γ} σ (v : Val Γ σ) → renV id v ≅ v
  renVid ι       v = renNid ι v
  renVid (σ ⇒ τ) v = refl

  renVcomp : ∀{Δ Γ B}(ρ : Ren Δ Γ)(ρ' : Ren Γ B) σ (v : Val Δ σ) → 
         renV (ρ' • ρ) v ≅ renV ρ' (renV ρ v)
  renVcomp ρ ρ' ι       v = renNcomp ρ ρ' ι v
  renVcomp ρ ρ' (σ ⇒ τ) v = refl


  renV<< : ∀{B' B Γ}(α  : Ren B B')(β : Env Γ B){σ}(v : Val B σ) →
        ∀{ρ}(y : Var (Γ < σ) ρ) → 
        ((renV α • β) << renV α v) y ≅ (renV α • (β << v)) y
  renV<< α β v vz = refl
  renV<< α β v (vs y) = refl


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


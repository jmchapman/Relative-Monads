{-# OPTIONS --type-in-type #-}
module WellTypedTerms3 where

open import Utilities
open import Categories
open import Functors
open import Naturals
open import Equality
open import RMonads2
open import FunctorCat
open import Sets
open import Families
open NatT

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀{Γ σ} → Var (Γ < σ) σ
  vs : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ

data Tm : Con → Ty → Set where
  var : ∀{Γ σ} → Var Γ σ → Tm Γ σ
  app : ∀{Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  lam : ∀{Γ σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)

Ren : Con → Con → Set
Ren Γ Δ = ∀ {σ} → Var Γ σ → Var Δ σ 

renId : ∀{Γ} → Ren Γ Γ
renId = id

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f • g

ConCat : Cat 
ConCat = record{
  Obj  = Con; 
  Hom  = Ren;
  iden = renId;
  comp = renComp;
  idl  = iext λ _ → refl;
  idr  = iext λ _ → refl;
  ass  = iext λ _ → refl}

wk : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ < σ) (Δ < σ)
wk f vz     = vz
wk f (vs i) = vs (f i)

ren : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren f (var x)   = var (f x)
ren f (app t u) = app (ren f t) (ren f u)
ren f (lam t)   = lam (ren (wk f) t)

wkid : ∀{Γ σ τ}(x : Var (Γ < τ) σ) → wk renId x ≅ renId x
wkid vz     = refl
wkid (vs x) = refl

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅ id t
renid (var x)   = refl
renid (app t u) = resp2 app (renid t) (renid u)
renid (lam t) = resp lam (trans (resp (λ (f : Ren _ _) → ren f t) 
                                      (iext (λ _ → ext wkid))) 
                                (renid t))

wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) → 
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x  
wkcomp f g vz     = refl
wkcomp f g (vs i) = refl

rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≅ (ren f • ren g) t
rencomp f g (var x)   = refl
rencomp f g (app t u) = resp2 app (rencomp f g t) (rencomp f g u)
rencomp f g (lam t)   = resp lam (trans (resp (λ (f : Ren _ _) → ren f t)
                                              (iext λ _ → ext (wkcomp f g)))
                                        (rencomp (wk f) (wk g) t))

Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f vz     = var vz
lift f (vs x) = ren vs (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (app t u) = app (sub f t) (sub f u)
sub f (lam t)   = lam (sub (lift f) t)

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f • g

liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≅ subId x
liftid vz     = refl
liftid (vs x) = refl

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ id t
subid (var x)   = refl
subid (app t u) = resp2 app (subid t) (subid u)
subid (lam t)   = resp lam (trans (resp (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))

-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f • wk g) x ≅ lift (f • g) x
liftwk f g vz     = refl
liftwk f g (vs x) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f • ren g) t ≅ sub (f • g) t
subren f g (var x)   = refl
subren f g (app t u) = resp2 app (subren f g t) (subren f g u)
subren f g (lam t)   = resp lam (trans (subren (lift f) (wk g) t)
                                       (resp (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → ext (liftwk f g))))

renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) • lift g) x ≅ lift (ren f • g) x
renwklift f g vz     = refl
renwklift f g (vs x) = trans (sym (rencomp (wk f) vs (g x))) 
                                (rencomp vs f (g x))

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f •  sub g) t ≅ sub (ren f • g) t
rensub f g (var x)   = refl
rensub f g (app t u) = resp2 app (rensub f g t) (rensub f g u)
rensub f g (lam t)   = resp lam (trans (rensub (wk f) (lift g) t) 
                                       (resp (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → 
                                               ext (renwklift f g))))

liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≅ subComp (lift f) (lift g) x
liftcomp f g vz     = refl
liftcomp f g (vs x) = trans (rensub vs f (g x))
                            (sym (subren (lift f) vs (g x)))

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≅ (sub f • sub g) t
subcomp f g (var x)   = refl
subcomp f g (app t u) = resp2 app (subcomp f g t) (subcomp f g u)
subcomp f g (lam t)   = resp lam (trans (resp (λ (f : Sub _ _) → sub f t) 
                                              (iext λ _ → ext (liftcomp f g))) 
                                        (subcomp (lift f) (lift g) t))
VarF : Fun ConCat (Fam Ty)
VarF = record { 
  OMap  = Var; 
  HMap  = id; 
  fid   = refl;
  fcomp = refl }

TmRMonad : RMonad VarF
TmRMonad = record { 
  T    = Tm; 
  η    = var; 
  bind = sub; 
  law1 = iext λ _ → ext subid ;
  law2 = refl; 
  law3 = λ{_ _ _ f g} → iext λ σ → ext (subcomp g f)}
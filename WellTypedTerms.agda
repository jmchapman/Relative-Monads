{-# OPTIONS --type-in-type #-}
module WellTypedTerms where

open import Library
open import Categories
open import Functors
open import RMonads
open import FunctorCat
open import Categories.Sets
open import Categories.Families

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
renComp f g = f ∘ g

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
renid (app t u) = 
  proof 
  app (ren renId t) (ren renId u) 
  ≅⟨ cong₂ app (renid t) (renid u) ⟩ 
  app t u 
  ∎
renid (lam t)   = 
  proof lam (ren (wk renId) t) 
  ≅⟨ cong (λ (f : Ren _ _) → lam (ren f t)) (iext λ _ → ext wkid) ⟩ 
  lam (ren renId t) 
  ≅⟨ cong lam (renid t) ⟩ 
  lam t 
  ∎ 

wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) → 
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x  
wkcomp f g vz     = refl
wkcomp f g (vs i) = refl

rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≅ (ren f ∘ ren g) t
rencomp f g (var x)   = refl
rencomp f g (app t u) = 
  proof
  app (ren (renComp f g) t) (ren (renComp f g) u)
  ≅⟨ cong₂ app (rencomp f g t) (rencomp f g u) ⟩
  app (ren f (ren g t)) (ren f (ren g u)) 
  ∎
rencomp f g (lam t)   = 
  proof
  lam (ren (wk (renComp f g)) t) 
  ≅⟨ cong (λ (f : Ren _ _) → lam (ren f t)) (iext λ _ → ext (wkcomp f g)) ⟩
  lam (ren (renComp (wk f) (wk g)) t)
  ≅⟨ cong lam (rencomp (wk f) (wk g) t) ⟩
  lam (ren (wk f) (ren (wk g) t)) 
  ∎

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
subComp f g = sub f ∘ g

liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≅ subId x
liftid vz     = refl
liftid (vs x) = refl

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ id t
subid (var x)   = refl
subid (app t u) = 
  proof 
  app (sub subId t) (sub subId u) 
  ≅⟨ cong₂ app (subid t) (subid u) ⟩ 
  app t u 
  ∎
subid (lam t)   = 
  proof 
  lam (sub (lift subId) t)
  ≅⟨ cong (λ (f : Sub _ _) → lam (sub f t)) (iext λ _ → ext liftid) ⟩ 
  lam (sub subId t) 
  ≅⟨ cong lam (subid t) ⟩ 
  lam t 
  ∎

-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f ∘ wk g) x ≅ lift (f ∘ g) x
liftwk f g vz     = refl
liftwk f g (vs x) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g (var x)   = refl
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
  ≅⟨ cong (λ (f : Sub _ _) → lam (sub f t)) (iext (λ _ → ext (liftwk f g))) ⟩
  lam (sub (lift (f ∘ g)) t) ∎ 

renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) ∘ lift g) x ≅ lift (ren f ∘ g) x
renwklift f g vz     = refl
renwklift f g (vs x) = 
  proof 
  ren (wk f) (ren vs (g x)) 
  ≅⟨ sym (rencomp (wk f) vs (g x)) ⟩ 
  ren (wk f ∘ vs) (g x)
  ≅⟨ rencomp vs f (g x) ⟩ 
  ren vs (ren f (g x)) 
  ∎

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≅ sub (ren f ∘ g) t
rensub f g (var x)   = refl
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
  lam (sub (ren (wk f) ∘ lift g) t)
  ≅⟨ cong (λ (f₁ : Sub _ _) → lam (sub f₁ t)) 
          (iext (λ _ → ext (renwklift f g))) ⟩
  lam (sub (lift (ren f ∘ g)) t) 
  ∎

liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≅ subComp (lift f) (lift g) x
liftcomp f g vz     = refl
liftcomp f g (vs x) = 
  proof 
  ren vs (sub f (g x)) 
  ≅⟨ rensub vs f (g x) ⟩ 
  sub (ren vs ∘ f) (g x)
  ≅⟨ sym (subren (lift f) vs (g x)) ⟩ 
  sub (lift f) (ren vs (g x)) 
  ∎ 

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g (var x)   = refl
subcomp f g (app t u) = 
  proof 
  app (sub (subComp f g) t) (sub (subComp f g) u)
  ≅⟨ cong₂ app (subcomp f g t) (subcomp f g u) ⟩
  app (sub f (sub g t)) (sub f (sub g u))
  ∎
subcomp f g (lam t)   = 
  proof
  lam (sub (lift (subComp f g)) t) 
  ≅⟨ cong (λ (f : Sub _ _) → lam (sub f t))
          (iext λ _ → ext (liftcomp f g)) ⟩
  lam (sub (subComp (lift f) (lift g)) t)
  ≅⟨ cong lam (subcomp (lift f) (lift g) t) ⟩
  lam (sub (lift f) (sub (lift g) t)) ∎ 

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

sub<< : ∀{Γ Δ σ}(f : Sub Γ Δ)(t : Tm Δ σ) → Sub (Γ < σ) Δ
sub<< f t vz     = t
sub<< f t (vs x) = f x 

lem1 : ∀{B Γ Δ σ}{f : Sub Γ Δ}{g : Ren B Γ}{t : Tm Δ σ}{τ}(x : Var (B < σ) τ) → 
        (sub<< f t ∘ wk g) x ≅ (sub<< (f ∘ g) t) x
lem1 vz     = refl
lem1 (vs x) = refl

lem2 : ∀{B Γ Δ σ}{f : Sub Γ Δ}{g : Sub B Γ}{t : Tm Δ σ}{τ}(x : Var (B < σ) τ) → 
       (subComp (sub<< f t) (lift g)) x ≅ (sub<< (subComp f g) t) x
lem2 vz     = refl
lem2 {f = f}{g = g}{t = t} (vs x) = subren (sub<< f t) vs (g x) 
                                          

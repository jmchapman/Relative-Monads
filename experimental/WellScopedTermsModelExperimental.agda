{-# OPTIONS --type-in-type --copatterns #-}

module experimental.WellScopedTermsModelExperimental where

open import Library hiding (proof_; _∎)
open import WellScopedTerms
open import RMonads
open import RMonads.REM
open import Categories.Sets
open import experimental.Delay 
--  hiding (_~_; module _~_; _∞~_; module _∞~_; ~force; ~refl; ∞~refl)
open import Size
open import Data.Empty
{-
mutual
  _$$_ : Val → Val → Val
  clo γ t $$ v = ev (γ << v) t

  ev : ∀{n} → Env n → Tm n → Val
  ev γ (var x) = γ x
  ev γ (lam t) = clo γ t
  ev γ (app t u) = ev γ t $$ ev γ u
-}

module EnvVal where
  mutual
    Env : ℕ → Set
    Env n = Fin n → Val
  
    data Val : Set where
      clo : ∀{n} → Env n → Tm (suc n) → Val
  
  _<<_ : ∀{n} → Env n → Val → Env (suc n)
  (γ << v) zero    = v
  (γ << v) (suc n) = γ n
    
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
  
-- here the env contains delayed values
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


postulate valeq : ∀{f f' : Val} →  
                  (∀ v → _~_ {∞} (force {∞} (f ∞$$ v)) (force {∞} (f' ∞$$ v))) →
                  f ≅ f'

cong-now : ∀ {A}{a a' : A} → a ≅ a' → now a ~⟨ ∞ ⟩~ now a'
cong-now refl = ~now _

cong-<< : ∀{n}{γ γ' : Env n} → (∀ x → γ x ~⟨ ∞ ⟩~ γ' x) → ∀{v v'} → v ≅ v' → 
              ∀(x : Fin (suc n)) → (γ << v) x ~⟨ ∞ ⟩~ (γ' << v') x
cong-<< p q zero    = cong-now q
cong-<< p q (suc x) = p x

cong-ev : ∀{n}{γ γ' : Env n} → (∀ x → γ x ~⟨ ∞ ⟩~ γ' x) → 
          (t : Tm n) → ev γ t ~⟨ ∞ ⟩~ ev γ' t
cong-ev p (var x)   = p x
cong-ev p (lam t)   = cong-now $ valeq λ v → cong-ev (cong-<< p refl) t
cong-ev {γ = γ}{γ' = γ'} p (app t u) = 
  proof
  (ev γ t >>= (λ f → ev γ u >>= (λ v → later (f ∞$$ v))))
  ~⟨ bind-cong-l (cong-ev p t) _ ⟩
  (ev γ' t >>= (λ f → ev γ u >>= (λ v → later (f ∞$$ v))))
  ~⟨ bind-cong-r (ev γ' t) (λ f → bind-cong-l (cong-ev p u) _) ⟩
  (ev γ' t >>= (λ f → ev γ' u >>= (λ v → later (f ∞$$ v))))
  ∎ where open ~-Reasoning

wk<< : ∀{m n}(α  : Ren m n)(β : Env n)
       (v : Val) → (y : Fin (suc m)) → 
       ((β ∘ α) << v) y ~⟨ ∞ ⟩~ (β << v) (wk α y)
wk<< α β v zero    = ~now _
wk<< α β v (suc i) = ~refl _

reneval : ∀{m n}(α : Ren m n)(β : Env n)
            (t : Tm m) → ev (β ∘ α) t ~⟨ ∞ ⟩~ (ev β ∘ ren α) t
reneval α β (var x) = ~refl _
reneval α β (lam t) = cong-now $ valeq λ v → 
  proof
  ev ((λ x → β (α x)) << v) t 
  ~⟨ cong-ev (wk<< α β v) t ⟩ 
  ev (λ x → (β << v) (wk α x)) t 
  ~⟨ reneval (wk α) (β << v) t ⟩ 
  ev (β << v) (ren (wk α) t) 
  ∎ where open ~-Reasoning
reneval α β (app t u) = 
  proof
  (ev (λ x → β (α x)) t >>= 
      (λ f → ev (λ x → β (α x)) u >>= (λ v → later (f ∞$$ v))))
  ~⟨ bind-cong-l (reneval α β t) _ ⟩
  (ev β (ren α t) >>= 
      (λ f → ev (λ x → β (α x)) u >>= (λ v → later (f ∞$$ v))))
  ~⟨ bind-cong-r (ev β (ren α t)) (λ f → bind-cong-l (reneval α β u) _) ⟩
  (ev β (ren α t) >>= (λ f → ev β (ren α u) >>= (λ v → later (f ∞$$ v))))
  ∎ where open ~-Reasoning

lift<< : ∀{m n}(γ  : Sub m n)(α : Env n)
         (a  : Val)(i : Fin (suc m)) → 
         ((λ x → ev α (γ x)) << a) i ~⟨ ∞ ⟩~ (ev (α << a) ∘ lift γ) i
lift<< γ α a zero    = ~now _
lift<< γ α a (suc i) = reneval suc (α << a) (γ i)

subeval : ∀{m n}(k : Sub m n)(f : Env n)(t : Tm m) →
 (ev  (λ x {i} → ev {i} f (k x)) t) ~⟨ ∞ ⟩~ (ev f (sub k t))
subeval k f (var x)   = ~refl _
subeval k f (lam t)   = cong-now $ valeq λ v →
  proof 
  ev ((λ x {i} → ev f (k x)) << v) t
  ~⟨ cong-ev (lift<< k f v) t ⟩ 
  ev (λ x {i} → ev (f << v) (lift k x)) t
  ~⟨ subeval (lift k) (f << v) t ⟩ 
  ev (f << v) (sub (lift k) t)
  ∎
  where open ~-Reasoning
subeval k f (app t u) = 
  proof
  (ev (λ x → ev f (k x)) t >>=
    (λ f₁ → ev (λ x → ev f (k x)) u >>= (λ v → later (f₁ ∞$$ v))))
  ~⟨ bind-cong-l (subeval k f t) _ ⟩
  (ev f (sub k t) >>=
    (λ f₁ → ev (λ x → ev f (k x)) u >>= (λ v → later (f₁ ∞$$ v))))
  ~⟨ bind-cong-r (ev f (sub k t)) (λ f₁ → bind-cong-l (subeval k f u) _) ⟩
  (ev f (sub k t) >>= (λ f₁ → ev f (sub k u) >>= (λ v → later (f₁ ∞$$ v))))
  ∎ 
  where open ~-Reasoning



TmRAlg : RAlg TmRMonad
TmRAlg  = record{
  acar  = ∀ {i} → Delay i Val; --S;
  astr  = λ γ t → ev γ t;
  alaw1 = refl;
  alaw2 = {!!}} -- ext λ t → subeval t _ _}       

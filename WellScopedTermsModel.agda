{-# OPTIONS --type-in-type #-}

module WellScopedTermsModel where

open import Function
open import WellScopedTerms
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Equality
open import RMonads
open import REM
open import Categories.Sets
open import Data.Fin hiding (lift)
open import Data.Nat

_<<_ : ∀{n X} → (Fin n → X) → X → Fin (suc n) → X
(f << x) zero     = x
(f << x) (suc i) = f i

record LambdaModel : Set where
  field S      : Set
  Env = λ n → Fin n → S
  field eval   : ∀{n} → Env n → Tm n → S
        ap     : S → S → S
        lawvar : ∀{n}{i : Fin n}{γ : Env n} →
                 eval γ (var i) ≅ γ i
        lawapp : ∀{n}{t u : Tm n}{γ : Env n} → 
                 eval γ (app t u) ≅ ap (eval γ t) (eval γ u)
        lawlam : ∀{n}{t : Tm (suc n)}{γ : Env n}{s : S} →
                 ap (eval γ (lam t)) s ≅ eval (γ << s) t
        lawext : ∀{f g : S} → ((a : S) → ap f a ≅ ap g a) → f ≅ g

module Model (l : LambdaModel) where
  open LambdaModel l

  wk<< : ∀{m n}(α  : Ren m n)(β : Env n)
            (v : S) → (y : Fin (suc m)) → 
            ((β ∘ α) << v) y ≅ (β << v) (wk α y)
  wk<< α β v zero    = refl
  wk<< α β v (suc i) = refl
  
  reneval : ∀{m n}(α : Ren m n)(β : Env n)
            (t : Tm m) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
  reneval α β (var i) = 
    proof
    eval (β ∘ α) (var i) 
    ≅⟨ lawvar ⟩
    β (α i)
    ≅⟨ sym lawvar ⟩
    eval β (var (α i)) ∎
  reneval α β (lam t) = lawext λ a → 
    proof
    ap (eval (β ∘ α) (lam t)) a 
    ≅⟨ lawlam ⟩
    eval ((β ∘ α) << a) t
    ≅⟨ cong (λ (f : Env _) → eval f t) (ext (wk<< α β a)) ⟩
    eval ((β << a) ∘ wk α) t
    ≅⟨ reneval (wk α) (β << a) t ⟩
    eval (β << a) (ren (wk α) t)
    ≅⟨ sym lawlam ⟩
    ap (eval β (lam (ren (wk α) t))) a 
    ∎
  reneval α β (app t u) = 
    proof
    eval (β ∘ α) (app t u) 
    ≅⟨ lawapp ⟩
    ap (eval (β ∘ α) t) (eval (β ∘ α) u)
    ≅⟨ cong₂ ap (reneval α β t) (reneval α β u) ⟩
    ap (eval β (ren α t)) (eval β (ren α u))
    ≅⟨ sym lawapp ⟩
    eval β (app (ren α t) (ren α u))
    ∎
  
  lift<< : ∀{m n}(γ  : Sub m n)(α : Env n)
           (a  : S)(i : Fin (suc m)) → 
           ((eval α ∘ γ ) << a) i ≅ (eval (α << a) ∘ lift γ) i
  lift<< γ α a zero = 
    proof 
    a 
    ≅⟨ sym lawvar ⟩ 
    eval (α << a) (var zero)
    ∎
  lift<< γ α a (suc i) = 
    proof
    eval α (γ i)
    ≡⟨⟩
    eval ((α << a) ∘ suc) (γ i)
    ≅⟨ reneval suc (α << a) (γ i) ⟩
    eval (α << a) (ren suc (γ i))
    ∎
  
  subeval : ∀{m n}(t : Tm m)(γ : Sub m n)(α : Env n) → 
            eval (eval α ∘ γ) t  ≅ (eval α ∘ sub γ) t
  subeval (var i)   γ α = 
    proof
    eval (eval α ∘ γ) (var i) 
    ≅⟨ lawvar ⟩
    eval α (γ i)
    ∎
  subeval (lam t)   γ α = lawext λ a → 
    proof
    ap (eval (eval α ∘ γ) (lam t)) a
    ≅⟨ lawlam ⟩
    eval ((eval α ∘ γ) << a) t
    ≅⟨ cong (λ (f : Env _) → eval f t) (ext (lift<< γ α a)) ⟩
    eval (eval (α << a) ∘ lift γ) t
    ≅⟨ subeval t (lift γ) (α << a) ⟩
    eval (α << a) (sub (lift γ) t) 
    ≅⟨ sym lawlam ⟩
    ap (eval α (lam (sub (lift γ) t))) a 
    ∎
  subeval (app t u) γ α = 
    proof
    eval (eval α ∘ γ) (app t u) 
    ≅⟨ lawapp ⟩
    ap (eval (eval α ∘ γ) t) (eval (eval α ∘ γ) u)
    ≅⟨ cong₂ ap (subeval t γ α) (subeval u γ α) ⟩
    ap (eval α (sub γ t)) (eval α (sub γ u))
    ≅⟨ sym lawapp ⟩
    eval α (app (sub γ t) (sub γ u)) 
    ∎

  TmRAlg : RAlg TmRMonad
  TmRAlg = record{
    acar  = S;
    astr  = eval;
    alaw1 = ext λ _ → sym lawvar;
    alaw2 =  ext λ t → subeval t _ _}       
  

-- some experiments
open import Coinduction

data Delay (X : Set) : Set where
  now : X → Delay X
  later : ∞ (Delay X) → Delay X

dbind : ∀{X Y} → (X → Delay Y) → Delay X → Delay Y
dbind f (now x)   = f x
dbind f (later x) = later (♯ (dbind f (♭ x)))

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

{-
mutual
  ev : ∀{n} → Env n → Tm n → Delay Val
  ev γ (var x) = now (γ x)
  ev γ (lam t) = now (clo γ t)
  ev γ (app t u) = dbind (λ f → dbind (λ v → f $$ v) (ev γ u)) (ev γ t)

  _$$_ : Val → Val → Delay Val
  clo γ t $$ v = later (♯ ev (γ << v) t)
-}

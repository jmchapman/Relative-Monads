{-# OPTIONS --type-in-type #-}

module WellScopedTermsModel where

open import Utilities
open import WellScopedTerms
open import Nat
open import Fin
open import Equality
open import RMonads2
open import REM2
open import Sets

_<<_ : ∀{n X} → (Fin n → X) → X → Fin (s n) → X
(f << x) fz     = x
(f << x) (fs i) = f i

record LambdaModel : Set where
  field S      : Set
        eval   : ∀{n} → (Fin n → S) → Tm n → S
        ap     : S → S → S
        lawvar : ∀{n}{i : Fin n}{γ : Fin n → S} →
                 eval γ (var i) ≅ γ i
        lawapp : ∀{n}{t u : Tm n}{γ : Fin n → S} → 
                 eval γ (app t u) ≅ ap (eval γ t) (eval γ u)
        lawlam : ∀{n}{t : Tm (s n)}{γ : Fin n → S}{s : S} →
                 ap (eval γ (lam t)) s ≅ eval (γ << s) t
        lawext : ∀{f g : S} → ((a : S) → ap f a ≅ ap g a) → f ≅ g
open LambdaModel

wk<< : ∀(l : LambdaModel){m n}(α  : Fin m → Fin n)(β : Fin n → S l)
          (v : S l) → (y : Fin (s m)) → 
          ((β • α) << v) y ≅ (β << v) (wk α y)
wk<< l α β v fz     = refl
wk<< l α β v (fs i) = refl

reneval : ∀(l : LambdaModel){m n}(α : Fin m → Fin n)(β : Fin n → S l)
          (t : Tm m) →
          eval l (eval l β • (var • α)) t
          ≅
          (eval l β • ren α) t
reneval l α β (var i)   = lawvar l
reneval l {m} {n} α β (lam t)   = lawext l λ a → 
  trans (lawlam l) 
        (trans (trans (resp (λ (f : Fin _ → S l) → eval l f t) 
                            (ext λ i → trans (trans (resp (λ (f : Fin m → S l) 
                                                           → (f << a) i) 
                                                          (ext λ i → lawvar l))
                                                    (wk<< l α β a i)) 
                                             (sym (lawvar l))))
                      (reneval l (wk α) (β << a) t)) 
               (sym (lawlam l)))
reneval l α β (app t u) = trans (lawapp l) 
                                (trans (resp2 (ap l) 
                                              (reneval l α β t)
                                              (reneval l α β u)) 
                                       (sym (lawapp l)))


lift<< : ∀(l : LambdaModel){m n}(γ  : Fin m → Tm n)(α : Fin n → S l)
         (a  : S l)(i : Fin (s m)) → 
         ((eval l α • γ ) << a) i ≅ (eval l (α << a) • lift γ) i
lift<< l γ α a fz = sym (lawvar l)
lift<< l γ α a (fs i) = trans (resp (λ (f : Fin _ → S l) → eval l f (γ i)) 
                                    (ext λ i → sym (lawvar l)))
                              (reneval l fs (α << a) (γ i))


subeval : ∀(l : LambdaModel){m n}(t : Tm m)
          (γ : Fin m → Tm n)(α : Fin n → S l) → 
          eval l (eval l α • γ) t  ≅ (eval l α • sub γ) t
subeval l (var i)   γ α = lawvar l 
subeval l (lam t)   γ α = lawext l λ a → 
  trans (lawlam l) 
        (trans (trans (resp (λ (f : Fin _ → S l) → eval l f t) 
                            (ext (lift<< l γ α a)))
                      (subeval l t (lift γ) (α << a))) 
               (sym (lawlam l)))
subeval l (app t u) γ α = trans (lawapp l) 
                             (trans (resp2 (ap l) 
                                           (subeval l t γ α) 
                                           (subeval l u γ α)) 
                                    (sym (lawapp l)))
TmRAlg : LambdaModel → RAlg TmRMonad
TmRAlg l = record{
  acar  = S l;
  astr  = eval l;
  alaw1 = ext λ _ → sym (lawvar l);
  alaw2 =  ext λ t → subeval l t _ _}       
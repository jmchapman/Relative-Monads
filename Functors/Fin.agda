module Functors.Fin where

open import Library
open import Categories.Sets
open import Categories.Setoids
open import Categories
open import Categories.Initial
open import Categories.CoProducts
open import Functors
open import Isomorphism
open import Functors.FullyFaithful

open Cat
open Fun
open Iso

Nats : Cat {lzero}{lzero}
Nats = record{
  Obj  = ℕ; 
  Hom  = λ m n → Fin m → Fin n;
  iden = id;
  comp = λ f g → f ∘ g;
  idl  = refl;
  idr  = refl;
  ass  = refl}

-- initial object

initN : Init Nats zero
initN = record {
  i   = λ ();
  law = ext λ ()}

-- coproducts

extend : ∀ {m n} -> Fin m -> Fin (m + n)
extend zero    = zero
extend (suc i) = suc (extend i)

lift : ∀ m {n} -> Fin n -> Fin (m + n)
lift zero    i = i
lift (suc m) i = suc (lift m i)

case : ∀ (m : ℕ){n : ℕ}{X : Set} →
  (Fin m → X) → (Fin n → X) → Fin (m + n) → X
case zero    f g i       = g i
case (suc m) f g zero    = f zero
case (suc m) f g (suc i) = case m (f ∘ suc) g i

lem1 : ∀ A {B C}(f : Fin A → C) (g : Fin B → C)(i : Fin A) →
  case A f g (extend i) ≅ f i
lem1 zero f g ()
lem1 (suc A) f g zero    = refl
lem1 (suc A) f g (suc i) = lem1 A (f ∘ suc) g i

lem2 : ∀ A {B C} (f : Fin A → C) (g : Fin B → C)(i : Fin B) → 
  case A f g (lift A i) ≅ g i
lem2 zero f g zero    = refl
lem2 zero f g (suc i) = refl
lem2 (suc A) f g i    = lem2 A (f ∘ suc) g i

lem3 : ∀ A {B C}(f : Fin A → C) (g : Fin B → C)
  (h : Fin (A + B) → C) →
  (λ x → h (extend {A} x)) ≅ f →
  (λ x → h (lift A x)) ≅ g → ∀ i → h i ≅ case A f g i
lem3 zero    f g h p q i       = fcong i q
lem3 (suc A) f g h p q zero    = fcong zero p
lem3 (suc A) f g h p q (suc i) =
  lem3 A (f ∘ suc) g (h ∘ suc) (ext (λ i → fcong (suc i) p)) q i  

coprod : CoProd Nats
coprod = record
  { _+_   = _+_
  ; inl   = extend
  ; inr   = λ{m} → lift m
  ; [_,_] = λ{m} → case m
  ; law1  = λ{m} f g → ext (lem1 m f g)
  ; law2  = λ{m} f g → ext (lem2 m f g)
  ; law3  = λ{m} f g h p q → ext (lem3 m f g h p q)
  }

--

FinF : Fun Nats Sets
FinF = record {
  OMap  = Fin;
  HMap  = id;
  fid   = refl;
  fcomp = refl}

FinFoid : Fun Nats Setoids
FinFoid = record {
  OMap  = λ n → record {
    set  = Fin n ; 
    eq   = λ i j → i ≅ j;
    ref  = refl; 
    sym' = sym;
    trn  = trans};
  HMap  = λ f → record {
    fun = f; feq = cong f};
  fid   = SetoidFunEq refl (iext λ _ → iext λ _ → ext congid);
  fcomp = λ{_ _ _ f g} → 
    SetoidFunEq refl (iext λ _ → iext λ _ → ext (congcomp f g))}

FinFF : FullyFaithful FinF
FinFF X Y = record {
  fun  = id;
  inv  = id;
  law1 = λ _ → refl;
  law2 = λ _ → refl}

open import Data.Bool

feq : forall {n} -> Fin n -> Fin n -> Bool
feq zero    zero    = true
feq zero    (suc j) = false
feq (suc i) zero    = false
feq (suc i) (suc j) = true

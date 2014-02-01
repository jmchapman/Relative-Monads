{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.conv:10 -v tc.conv.size:15 #-}
module Delay where

open import Library

-- Coinductive delay monad.

mutual

  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay A j

open ∞Delay public

-- Smart constructor.

later! : ∀ {A i} → Delay A i → Delay A (↑ i)
later! x = later (delay x)

-- Monad instance.

module Bind where
  mutual
    _>>=_ : ∀ {i A B} → Delay A i → (A → Delay B i) → Delay B i
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay A i → (A → Delay B i) → ∞Delay B i
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → Delay A i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) 
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

-- Map for ∞Delay

_∞<$>_ : ∀ {i A B} (f : A → B) (∞a : ∞Delay A i) → ∞Delay B i
f ∞<$> ∞a = ∞a ∞>>= λ a → return (f a)
-- force (f ∞<$> ∞a) = f <$> force ∞a

-- Double bind

_=<<2_,_ : ∀ {i A B C} → (A → B → Delay C i) → Delay A i → Delay B i → Delay C i
f =<<2 x , y = x >>= λ a → y >>= λ b → f a b

-- Strong bisimilarity

mutual
  data _~_ {i : Size} {A : Set} : (a? b? : Delay A ∞) → Set where
    ~now   : ∀ a → now a ~ now a
    ~later : ∀ {a∞ b∞} (eq : _∞~_ {i} a∞ b∞) → later a∞ ~ later b∞

  record _∞~_ {i : Size} {A : Set} (a∞ b∞ : ∞Delay A ∞) : Set where
    constructor ~delay
    field
      ~force : {j : Size< i} → _~_ {j} (force a∞) (force b∞)

open _∞~_ public

-- Reflexivity

mutual
  ~refl  : ∀ {i A} (a? : Delay A ∞) → _~_ {i} a? a?
  ~refl (now a)    = ~now a
  ~refl (later a∞) = ~later (∞~refl a∞)

  ∞~refl : ∀ {i A} (a∞ : ∞Delay A ∞) → _∞~_ {i} a∞ a∞
  ~force (∞~refl a∞) = ~refl (force a∞)

-- Symmetry

mutual
  ~sym : ∀ {i A} {a? b? : Delay A ∞} → _~_ {i} a? b? → _~_ {i} b? a?
  ~sym (~now a)    = ~now a
  ~sym (~later eq) = ~later (∞~sym eq)

  ∞~sym : ∀ {i A} {a? b? : ∞Delay A ∞} → _∞~_ {i} a? b? → _∞~_ {i} b? a?
  ~force (∞~sym eq) = ~sym (~force eq)

-- Transitivity

mutual
  ~trans : ∀ {i A} {a? b? c? : Delay A ∞}
    (eq : _~_ {i} a? b?) (eq' : _~_ {i} b? c?) → _~_ {i} a? c?
  ~trans (~now a)    (~now .a)    = ~now a
  ~trans (~later eq) (~later eq') = ~later (∞~trans eq eq')

  ∞~trans : ∀ {i A} {a∞ b∞ c∞ : ∞Delay A ∞}
    (eq : _∞~_ {i} a∞ b∞) (eq' : _∞~_ {i} b∞ c∞) → _∞~_ {i} a∞ c∞
  ~force (∞~trans eq eq') = ~trans (~force eq) (~force eq')

-- Equality reasoning

~setoid : (i : Size) (A : Set) → Setoid lzero lzero
~setoid i A = record
  { Carrier       = Delay A ∞
  ; _≈_           = _~_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ~refl a?
    ; sym   = ~sym
    ; trans = ~trans
    }
  }

module ~-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (~setoid i A)) public
--    using (begin_; _∎) (_≈⟨⟩_ to _~⟨⟩_; _≈⟨_⟩_ to _~⟨_⟩_)
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _~⟨_⟩_; begin_ to proof_)

∞~setoid : (i : Size) (A : Set) → Setoid lzero lzero
∞~setoid i A = record
  { Carrier       = ∞Delay A ∞
  ; _≈_           = _∞~_ {i}
  ; isEquivalence = record
    { refl  = λ {a?} → ∞~refl a?
    ; sym   = ∞~sym
    ; trans = ∞~trans
    }
  }

module ∞~-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (∞~setoid i A)) public
--    using (begin_; _∎) (_≈⟨⟩_ to _~⟨⟩_; _≈⟨_⟩_ to _~⟨_⟩_)
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∞~⟨_⟩_; begin_ to proof_)


-- Congruence laws.

mutual
  bind-cong-l : ∀ {i A B} {a? b? : Delay A ∞} (eq : _~_ {i} a? b?)
    (k : A → Delay B ∞) → _~_ {i} (a? >>= k) (b? >>= k)
  bind-cong-l (~now a)    k = ~refl _
  bind-cong-l (~later eq) k = ~later (∞bind-cong-l eq k)

  ∞bind-cong-l : ∀ {i A B} {a∞ b∞ : ∞Delay A ∞} (eq : _∞~_ {i} a∞ b∞) →
    (k : A → Delay B ∞) →
    _∞~_ {i} (a∞ ∞>>= k)  (b∞ ∞>>= k)
  ~force (∞bind-cong-l eq k) = bind-cong-l (~force eq) k

_>>=l_ = bind-cong-l

mutual
  bind-cong-r : ∀ {i A B} (a? : Delay A ∞) {k l : A → Delay B ∞} →
    (h : ∀ a → _~_ {i} (k a) (l a)) → _~_ {i} (a? >>= k) (a? >>= l)
  bind-cong-r (now a)    h = h a
  bind-cong-r (later a∞) h = ~later (∞bind-cong-r a∞ h)

  ∞bind-cong-r : ∀ {i A B} (a∞ : ∞Delay A ∞) {k l : A → Delay B ∞} →
    (h : ∀ a → _~_ {i} (k a) (l a)) → _∞~_ {i} (a∞ ∞>>= k)  (a∞ ∞>>= l)
  ~force (∞bind-cong-r a∞ h) = bind-cong-r (force a∞) h

_>>=r_ = bind-cong-r

mutual
  bind-cong : ∀ {i A B}  {a? b? : Delay A ∞} (eq : _~_ {i} a? b?)
              {k l : A → Delay B ∞} (h : ∀ a → _~_ {i} (k a) (l a)) →
              _~_ {i} (a? >>= k) (b? >>= l)
  bind-cong (~now a)    h = h a
  bind-cong (~later eq) h = ~later (∞bind-cong eq h)

  ∞bind-cong : ∀ {i A B} {a∞ b∞ : ∞Delay A ∞} (eq : _∞~_ {i} a∞ b∞)
    {k l : A → Delay B ∞} (h : ∀ a → _~_ {i} (k a) (l a)) →
    _∞~_ {i} (a∞ ∞>>= k)  (b∞ ∞>>= l)
  ~force (∞bind-cong eq h) = bind-cong (~force eq) h

_~>>=_ = bind-cong

-- Monad laws.

mutual
  bind-assoc : ∀{i A B C}(m : Delay A ∞)
               {k : A → Delay B ∞}{l : B → Delay C ∞} →
               _~_ {i} ((m >>= k) >>= l)  (m >>= λ a → k a >>= l)
  bind-assoc (now a)    = ~refl _
  bind-assoc (later a∞) = ~later (∞bind-assoc a∞)

  ∞bind-assoc : ∀{i A B C}(a∞ : ∞Delay A ∞)
                {k : A → Delay B ∞}{l : B → Delay C ∞} →
                _∞~_ {i} ((a∞ ∞>>= λ a → k a) ∞>>= l) (a∞ ∞>>= λ a → k a >>= l)
  ~force (∞bind-assoc a∞) = bind-assoc (force a∞)

-- Termination/Convergence.  Makes sense only for Delay A ∞.

data _⇓_ {A : Set} : (a? : Delay A ∞) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay A ∞} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay A ∞) → Set
x ⇓ = ∃ λ a → x ⇓ a

-- Monotonicity.

map⇓ : ∀ {A B} {a : A} {a? : Delay A ∞}
  (f : A → B) (a⇓ : a? ⇓ a) → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

-- some lemmas about convergence
subst~⇓ : ∀{A}{t t' : Delay A ∞}{n : A} → t ⇓ n → t ~ t' → t' ⇓ n
subst~⇓ now⇓ (~now a) = now⇓
subst~⇓ (later⇓ p) (~later eq) = later⇓ (subst~⇓ p (~force eq))

-- this should also hold for weak bisimularity right?
{-
subst≈⇓ : ∀{A}{t t' : Delay A ∞}{n : A} → t ⇓ n → t ≈ t' → t' ⇓ n
subst≈⇓ = ?
-}


⇓>>= : ∀{A B}(f : A → Delay B ∞)
       {?a : Delay A ∞}{a : A} → ?a ⇓ a → 
       {b : B} → (?a >>= f) ⇓ b → f a ⇓ b
⇓>>= f now⇓ q = q
⇓>>= f (later⇓ p) (later⇓ q) = ⇓>>= f p q

>>=⇓ : ∀{A B}(f : A → Delay B ∞)
       {?a : Delay A ∞}{a : A} → ?a ⇓ a → 
       {b : B} → f a ⇓ b → (?a >>= f) ⇓ b
>>=⇓ f now⇓ q = q
>>=⇓ f (later⇓ p) q = later⇓ (>>=⇓ f p q)

-- handy when you can't pattern match like in a let definition
unlater : ∀{A}{∞a : ∞Delay A ∞}{a : A} → later ∞a ⇓ a → force ∞a ⇓ a
unlater (later⇓ p) = p 








{-
mutual
  _⇓_ : {A : Set} {i : Size} (x : Delay A i) (a : A) → Set
  x ⇓ a = Terminates a x

  data Terminates {A : Set} {i : Size} (a : A) : Delay A i → Set where
    now   : now a ⇓ a
    later : ∀ {x : ∞Delay A i} → (force x {j = ?}) ⇓ a → later x ⇓ a

mutual

  cast : ∀ {A i} → Delay A i → (j : Size< ↑ i) → Delay A j
  cast (now x) j = now x
  cast (later x) j = {!later (∞cast x j)!}

  ∞cast : ∀ {A i} → ∞Delay A i → (j : Size< ↑ i) → ∞Delay A j
  ♭ (∞cast x j) {k} = cast {i = j} (♭ x) k
-}

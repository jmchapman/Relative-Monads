module Library where

open import Function using (id; _∘_; _$_) public
open import Relation.Binary.HeterogeneousEquality public
open ≅-Reasoning renaming (begin_ to proof_) public
open import Data.Product renaming (proj₁ to fst; proj₂ to snd) public
open import Data.Empty public using (⊥)
open import Data.Unit public using (⊤)
open import Data.Nat public using (ℕ; zero; suc; _+_; module ℕ)
open import Data.Fin public using (Fin; zero; suc)
open import Level public renaming (suc to lsuc; zero to lzero) hiding (lift)

-- needed for setoids
congid : ∀{a}{A : Set a}{a a' : A}(p : a ≅ a') → cong id p ≅ p
congid refl = refl

congcomp : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
           {a a' : A}(f : B → C)(g : A → B)(p : a ≅ a') →
            cong (f ∘ g) p ≅ cong f (cong g p)
congcomp f g refl = refl

-- should be replaced by dcong
cong' : ∀{a b}{A A' : Set a} → A ≅ A' → 
        {B : A → Set b}{B' : A' → Set b} → B ≅ B' → 
        {f : ∀ a → B a}{f' : ∀ a → B' a} → f ≅ f' → 
        {a : A}{a' : A'} → a ≅ a' → f a ≅ f' a'
cong' refl refl refl refl = refl

-- should be replaced by dicong
icong' : ∀{a b}{A A' : Set a} → A ≅ A' → 
         {B : A → Set b}{B' : A' → Set b} → B ≅ B' → 
         {f : ∀ {a} → B a}{f' : ∀ {a} → B' a} → 
         (λ {a} → f {a}) ≅ (λ {a} → f' {a}) → 
         {a : A}{a' : A'} → a ≅ a' → f {a} ≅ f' {a'}
icong' refl refl refl refl = refl

fcong : ∀{a b}{A : Set a}{B : A → Set b}{f f' : (x : A) → B x}
        (a : A) → f ≅ f' → f a ≅ f' a
fcong a refl = refl

dcong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
        {f : (a : A) → B a}{f' : (a : A') → B' a}{a : A}{a' : A'} → 
        a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dcong refl refl refl = refl

dicong : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
         {f : ∀ {a} → B a}{f' : ∀ {a} → B' a} → {a : A}{a' : A'} → 
         a ≅ a' →  B ≅ B' → 
         (λ {a} → f {a}) ≅ (λ {a} → f' {a}) → 
         f {a} ≅ f' {a'}
dicong refl refl refl = refl

ifcong : ∀{a b}{A : Set a}{B : A → Set b}{f f' : {x : A} → B x}(a : A) → 
         _≅_ {_}{ {x : A} → B x} f { {x : A} → B x} f' → f {a} ≅ f' {a}
ifcong a refl = refl

cong₃ : ∀{a b c d}{A : Set a}{B : A → Set b}
        {C : ∀ x → B x → Set c }{D : ∀ x y → C x y → Set d}
        (f : ∀ x y z → D x y z)
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a b}{c' : C a' b'} → c ≅ c' → 
        f a b c ≅ f a' b' c'
cong₃ f refl refl refl = refl

ir : ∀{a}{A B : Set a}{x : A}{y : B}(p q : x ≅ y) → p ≅ q
ir refl refl = refl

stripsubst : ∀{a c}{A : Set a}(C : A → Set c) → 
             {a : A} → (c : C a) → 
             {b : A} → (p : a ≅ b) → 
             subst C p c ≅ c
stripsubst C c refl = refl 

postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}
                {f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g

postulate dext : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                 {f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ {a a'} → a ≅ a' → f a ≅ g a') → f ≅ g

-- this could just be derived from ext

postulate iext : ∀{a b}{A : Set a}{B B' : A → Set b}
                 {f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} ≅ g {a}) → 
                 _≅_ {_}{ {a : A} → B a} f { {a : A} → B' a} g

postulate diext : ∀{a b}{A A' : Set a}{B : A → Set b}{B' : A' → Set b}
                  {f : ∀ {a} → B a}{f' : ∀{a'} → B' a'} → 
                  (∀{a a'} → a ≅ a' → f {a} ≅ f' {a'}) → 
                  _≅_ {_}{ {a : A} → B a} f { {a' : A'} → B' a'} f'

hir : ∀{a}{A A' A'' A''' : Set a}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
hir {p = refl} {q = refl} refl = refl

hir' : ∀{a}{A A' A'' A''' : Set a}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} → a' ≅ a''' → p ≅ q
hir' {p = refl} {q = refl} refl = refl

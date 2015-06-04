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

congid : ∀{a}{A : Set a}{a a' : A}(p : a ≅ a') → cong id p ≅ p
congid refl = refl

congcomp : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
           {a a' : A}(f : B → C)(g : A → B)(p : a ≅ a') →
            cong (f ∘ g) p ≅ cong f (cong g p)
congcomp f g refl = refl

icong : ∀{a b}{A : Set a}{B : A → Set b}(f : ∀ {a} → B a){a a' : A} → 
        a ≅ a' → f {a} ≅ f {a'}
icong f refl = refl

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

funnycong : ∀{a b c}{A : Set a}{B : A → Set b}{C : Set c}{a a' : A} → 
            a ≅ a' → {b : B a}{b' : B a'} → b ≅ b' → 
            (f : (a : A) → B a → C) → f a b ≅ f a' b'
funnycong refl refl f = refl

proof-irr : ∀{a}{A B : Set a}{x : A}{y : B}(p q : x ≅ y) → p ≅ q
proof-irr refl refl = refl


{-
funnyresp3 : ∀{A}{B : A → Set}{C : A → Set}{D : Set}
        (f : (x : A)(y : B x)(z : C x) → D)
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a}{c' : C a'} → c ≅ c' → 
        f a b c ≅ f a' b' c'
funnyresp3 f refl refl refl = refl
-}

funnycong4 : ∀{a b c d e}
             {A : Set a}{B : A → Set b}{C : (a : A) → B a → Set c}
             {D : (a : A)(b : B a) → C a b  → Set d}{E : Set e}
             (f : (a : A)(b : B a)(c : C a b) → D a b c → E) → 
             {a a' : A} → a ≅ a' → 
             {b : B a}{b' : B a'} → b ≅ b' → 
             {c : C a b}{c' : C a' b'} → c ≅ c' → 
             {d : D a b c}{d' : D a' b' c'} → d ≅ d' → 
             f a b c d ≅ f a' b' c' d'
funnycong4 f refl refl refl refl = refl

funnycong4' : ∀{a b c d e}{A : Set a}{B : A → Set b}{C : (a : A) → B a → Set c}
              {D : (a : A) → B a → Set d}{E : Set e}
              {a a' : A} → a ≅ a' → 
              {b : B a}{b' : B a'} → b ≅ b' → 
              {c : C a b}{c' : C a' b'} → c ≅ c' → 
              {d : D a b}{d' : D a' b'} → d ≅ d' → 
              (f : (a : A)(b : B a) → C a b → D a b → E) →
              f a b c d ≅ f a' b' c' d'
funnycong4' refl refl refl refl f = refl

{-
funnyresp12 : {A : Set}
              {B : A → Set}
              {C : (a : A) → B a → Set}
              {D : (a : A)(b : B a) → C a b  → Set}
              {E : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {F : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {G : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {H : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {I : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {J : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {K : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {L : (a : A)(b : B a)(c : C a b) → D a b c → Set}
              {M : Set}
              {a a' : A} → a ≅ a' → 
              {b : B a}{b' : B a'} → b ≅ b' → 
              {c : C a b}{c' : C a' b'} → c ≅ c' → 
              {d : D a b c}{d' : D a' b' c'} → d ≅ d' → 
              {e : E a b c d}{e' : E a' b' c' d'} → e ≅ e' →
              {f : F a b c d}{f' : F a' b' c' d'} → f ≅ f' →
              {g : G a b c d}{g' : G a' b' c' d'} → g ≅ g' →
              {h : H a b c d}{h' : H a' b' c' d'} → h ≅ h' →
              {i : I a b c d}{i' : I a' b' c' d'} → i ≅ i' →
              {j : J a b c d}{j' : J a' b' c' d'} → j ≅ j' →
              {k : K a b c d}{k' : K a' b' c' d'} → k ≅ k' →
              {l : L a b c d}{l' : L a' b' c' d'} → l ≅ l' →
              (m : (a : A)
                   (b : B a)
                   (c : C a b)
                   (d : D a b c) → 
                   E a b c d → 
                   F a b c d → 
                   G a b c d → 
                   H a b c d → 
                   I a b c d → 
                   J a b c d → 
                   K a b c d → 
                   L a b c d → 
                   M) → 
              m a b c d e f g h i j k l ≅ m a' b' c' d' e' f' g' h' i' j' k' l'
funnyresp12 refl refl refl refl refl refl refl refl refl refl refl refl f = refl


subst : ∀{A}(P : A → Set){a a' : A} → a ≅ a' → P a → P a'
subst P refl p = p

substtrans : ∀{A}(P : A → Set){a a' a''}(p : a ≅ a')(q : a' ≅ a'') → 
             ∀ x → subst P (trans p q) x ≅ (subst P q • subst P p) x
substtrans P refl refl x = refl
-}

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

--ir : ∀ {A A' : Set}{a : A}{a' : A'}{p q : a ≅ a'} → p ≅ q
--ir {p = refl}{q = refl} = refl

fixtypes : ∀{a}{A A' A'' A''' : Set a}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
fixtypes {p = refl} {q = refl} refl = refl

fixtypes' : ∀{a}{A A' A'' A''' : Set a}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}
           {p : a ≅ a'}{q : a'' ≅ a'''} → a' ≅ a''' → p ≅ q
fixtypes' {p = refl} {q = refl} refl = refl

{-
infix  4 _IsRelatedTo_
infix  2 _∎
infixr 2 _≅⟨_⟩_ 
infix  1 begin_

data _IsRelatedTo_ {A : Set}(x : A){B : Set}(y : B) : Set where
  relTo : (x≅y : x ≅ y) → x IsRelatedTo y

begin_ : ∀{A : Set}{x : A}{B : Set}{y : B} → x IsRelatedTo y → x ≅ y
begin relTo x≅y = x≅y

_≅⟨_⟩_ : ∀{A : Set}(x : A){B : Set}{y : B}{C : Set}{z : C} →
         x ≅ y → y IsRelatedTo z → x IsRelatedTo z
_ ≅⟨ x≅y ⟩ relTo y≅z = relTo (trans x≅y y≅z)

_∎ : ∀ {A : Set} (x : A) → x IsRelatedTo x
_∎ _ = relTo refl
-}

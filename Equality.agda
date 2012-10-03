{-# OPTIONS --type-in-type #-}

module Equality where

open import Utilities

data _≅_ {A : Set} : {A' : Set} → A → A' → Set where
  refl : {a : A} → a ≅ a

infix 10 _≅_

trans : ∀{A A' A''}{a : A}{a' : A'}{a'' : A''} → a ≅ a' → a' ≅ a'' → a ≅ a''
trans refl p = p

sym : ∀{A A'}{a : A}{a' : A'} → a ≅ a' → a' ≅ a
sym refl = refl

resp : ∀{A}{B : A → Set}(f : ∀ a → B a){a a' : A} → a ≅ a' → f a ≅ f a'
resp f refl = refl

respid : ∀{A}{a a' : A}(p : a ≅ a') → resp id p ≅ p
respid refl = refl

respcomp : ∀{A B C}{a a' : A}(f : B → C)(g : A → B)(p : a ≅ a') →
            resp (f • g) p ≅ resp f (resp g p)
respcomp f g refl = refl

iresp : ∀{A}{B : A → Set}(f : ∀ {a} → B a){a a' : A} → a ≅ a' → f {a} ≅ f {a'}
iresp f refl = refl

fresp : ∀{A}{B : A → Set}{f f' : (x : A) → B x}(a : A) → f ≅ f' → f a ≅ f' a
fresp a refl = refl

dresp : ∀{A A' B B'}{f : A → B}{f' : A' → B'}{a : A}{a' : A'} → a ≅ a' → B ≅ B' → f ≅ f' → f a ≅ f' a'
dresp refl refl refl = refl


resp2 : ∀{A}{B : A → Set}{C : (x : A) → B x → Set}(f : (x : A)(y : B x) → C x y){a a' : A} → a ≅ a' → {b : B a}{b' : B a'} → b ≅ b' → f a b ≅ f a' b'
resp2 f refl refl = refl

ifresp : ∀{A}{B : A → Set}{f f' : {x : A} → B x}(a : A) → _≅_ { {x : A} → B x}{ {x : A} → B x} f f' → f {a} ≅ f' {a}
ifresp a refl = refl

funnyresp : ∀{A}{B : A → Set}{C : Set}{a a' : A} → a ≅ a' → {b : B a}{b' : B a'} → b ≅ b' → 
            (f : (a : A) → B a → C) → f a b ≅ f a' b'
funnyresp refl refl f = refl

funnyresp3 : ∀{A}{B : A → Set}{C : A → Set}{D : Set}
        (f : (x : A)(y : B x)(z : C x) → D)
        {a a' : A} → a ≅ a' → 
        {b : B a}{b' : B a'} → b ≅ b' → 
        {c : C a}{c' : C a'} → c ≅ c' → 
        f a b c ≅ f a' b' c'
funnyresp3 f refl refl refl = refl

funnyresp4 : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}{D : (a : A)(b : B a) → C a b  → Set}{E : Set}
             (f : (a : A)(b : B a)(c : C a b) → D a b c → E) → 
             {a a' : A} → a ≅ a' → 
             {b : B a}{b' : B a'} → b ≅ b' → 
             {c : C a b}{c' : C a' b'} → c ≅ c' → 
             {d : D a b c}{d' : D a' b' c'} → d ≅ d' → 
             f a b c d ≅ f a' b' c' d'
funnyresp4 f refl refl refl refl = refl

funnyresp4' : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}{D : (a : A) → B a → Set}{E : Set}
             {a a' : A} → a ≅ a' → 
             {b : B a}{b' : B a'} → b ≅ b' → 
             {c : C a b}{c' : C a' b'} → c ≅ c' → 
             {d : D a b}{d' : D a' b'} → d ≅ d' → 
            (f : (a : A)(b : B a) → C a b → D a b → E) → f a b c d ≅ f a' b' c' d'
funnyresp4' refl refl refl refl f = refl

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

stripsubst : {A : Set} → (C : A → Set) → {a : A} → (c : C a) → {b : A} → (p : a ≅ b) → subst C p c ≅ c
stripsubst C c refl = refl 

postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a ≅ g a) → f ≅ g

-- this could just be derived from ext
postulate iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} ≅ g {a}) → 
                 _≅_ { {a : A} → B a} { {a : A} → B' a} f g

postulate diext : {A A' : Set}{B : A → Set}{B' : A' → Set}{f : ∀ {a} → B a}{f' : ∀{a'} → B' a'} → (∀{a a'} → a ≅ a' → f {a} ≅ f' {a'}) → _≅_ { {a : A} → B a}{ {a' : A'} → B' a'} f f'

ir : ∀ {A A' : Set}{a : A}{a' : A'}{p q : a ≅ a'} → p ≅ q
ir {p = refl}{q = refl} = refl

fixtypes : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}{p : a ≅ a'}{q : a'' ≅ a'''} → a ≅ a'' → a' ≅ a''' → p ≅ q
fixtypes refl refl = ir        

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

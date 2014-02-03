open import Categories
open import Monads

module Monads.EM.Functors {a b}{C : Cat {a}{b}}(M : Monad C) where

open import Library
open import Functors
open import Monads.EM M

open Cat C
open Fun
open Monad M
open Alg
open AlgMorph 

EML : Fun C EM
EML = record {
  OMap = λ X → record {
    acar  = T X; 
    astr  = λ _ → bind; 
    alaw1 = sym law2; 
    alaw2 = law3};
  HMap = λ f → record {
    amor = bind (comp η f);
    ahom = λ {Z} {g} → 
      proof
      comp (bind (comp η f)) (bind g) 
      ≅⟨ sym law3 ⟩
      bind (comp (bind (comp η f)) g) 
      ∎};
  fid = AlgMorphEq (
    proof 
    bind (comp η iden) 
    ≅⟨ cong bind idr ⟩ 
    bind η 
    ≅⟨ law1 ⟩ 
    iden ∎);
  fcomp = λ {X}{Y}{Z}{f}{g} → 
    AlgMorphEq (
      proof 
      bind (comp η (comp f g)) 
      ≅⟨ cong bind (sym ass) ⟩
      bind (comp (comp η f) g) 
      ≅⟨ cong (λ f → bind (comp f g)) (sym law2) ⟩
      bind (comp (comp (bind (comp η f)) η) g)
      ≅⟨ cong bind ass ⟩
      bind (comp (bind (comp η f)) (comp η g))
      ≅⟨ law3 ⟩ 
      comp (bind (comp η f)) (bind (comp η g)) 
      ∎)}

EMR : Fun EM C
EMR  = record {
  OMap  = acar; 
  HMap  = amor;
  fid   = refl; 
  fcomp = refl}

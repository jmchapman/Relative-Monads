{-# OPTIONS --type-in-type #-}
open import Monads2
module EMAdj2 {C}(M : Monad C) where

open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)
open import Categories
open import Functors
open import Adjunctions2
open import EM2 M
open import EMFunctors2 M

open Cat C
open Fun
open Monad M
open Adj
open Alg
open AlgMorph

EMAdj : Adj C EM
EMAdj  = record {
  L = EML;
  R = EMR;
  left = λ f → comp (amor f) η;
  right = λ {X}{Y} f → 
    record{amor = astr Y X f;
           ahom = λ {Z}{g} → 
             proof
             comp (astr Y X f) (astr (OMap EML X) Z g)
             ≅⟨ sym (alaw2 Y) ⟩
             astr Y Z (comp (astr Y X f) g) 
             ∎};
  lawa = λ {X}{Y}(f : AlgMorph (OMap EML X) Y) → AlgMorphEq (
    proof 
    astr Y X (comp (amor f) η) 
    ≅⟨ sym (ahom f) ⟩ 
    comp (amor f) (astr (OMap EML X) X η)
    ≡⟨⟩
    comp (amor f) (bind η)
    ≅⟨ cong (comp (amor f)) law1 ⟩
    comp (amor f) iden
    ≅⟨ idr ⟩
    amor f 
    ∎);
  lawb = λ {X}{Y} f → 
    proof 
    comp (astr Y X f) η 
    ≅⟨ sym (alaw1 Y) ⟩ 
    f 
    ∎;
  natleft = λ{X}{X'}{Y}{Y'} f g h → 
    proof
    comp (amor g) (comp (comp (amor h) η) f) 
    ≅⟨ cong (comp (amor g)) ass ⟩
    comp (amor g) (comp (amor h) (comp η f))
    ≅⟨ cong (comp (amor g) ∘ comp (amor h)) (sym law2) ⟩
    comp (amor g) (comp (amor h) (comp (bind (comp η f)) η))
    ≅⟨ cong (comp (amor g)) (sym ass) ⟩
    comp (amor g) (comp (comp (amor h) (bind (comp η f))) η)
    ≅⟨ sym ass ⟩
    comp (comp (amor g) (comp (amor h) (bind (comp η f)))) η
    ∎;
  natright = λ{X}{X'}{Y}{Y'} f g h → 
    AlgMorphEq (trans (sym (ahom g)) 
                      (cong (comp (amor g)) 
                            (trans (cong (astr Y X') 
                                         (trans (cong (λ (g : Hom _ _) → 
                                                         comp g f) 
                                                      (alaw1 Y)) 
                                                ass)) 
                                   (alaw2 Y))))}

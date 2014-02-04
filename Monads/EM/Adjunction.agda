{-# OPTIONS --type-in-type #-}
open import Monads
module Monads.EM.Adjunction {C}(M : Monad C) where

open import Library
open import Categories
open import Functors
open import Adjunctions
open import Monads.EM M
open import Monads.EM.Functors M

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
  natright = λ{X}{X'}{Y}{Y'} f g h → AlgMorphEq (
    proof
    astr Y' X' (comp (amor g) (comp h f)) 
    ≅⟨ sym (ahom g) ⟩
    comp (amor g) (astr Y X' (comp h f))
    ≅⟨ cong (λ h → comp (amor g) (astr Y X' (comp h f))) (alaw1 Y) ⟩
    comp (amor g) (astr Y X' (comp (comp (astr Y X h) η) f))
    ≅⟨ cong (comp (amor g) ∘ astr Y X') ass ⟩
    comp (amor g) (astr Y X' (comp (astr Y X h) (comp η f)))
    ≅⟨ cong (comp (amor g)) (alaw2 Y) ⟩
    comp (amor g) (comp (astr Y X h) (bind (comp η f))) 
    ∎)}

{-# OPTIONS --type-in-type #-}
open import RMonads
open import Functors

module RMonads.CatofRAdj.TermRAdj {C D}{J : Fun C D}(M : RMonad J) where

open import Library
open import RAdjunctions
open import Categories
open import RMonads.CatofRAdj M
open import Categories.Terminal
open import RMonads.REM M
open import RMonads.REM.Adjunction M
open import RAdjunctions.RAdj2RMon
open import RMonads.CatofRAdj.TermRAdjObj M
open import RMonads.CatofRAdj.TermRAdjHom M
open import RMonads.CatofRAdj.TermRAdjUniq M

EMIsTerm : Term CatofAdj
EMIsTerm = record { 
  T   = EMObj; 
  t   = λ {X} → EMHom X; 
  law = uniq}

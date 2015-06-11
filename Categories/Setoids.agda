module Categories.Setoids where

open import Library
open import Categories


record Setoid {a b} : Set (lsuc (a ⊔ b)) where
  field set : Set a
        eq  : set → set → Set b
        ref : {s : set} → eq s s
        sym' : {s s' : set} → eq s s' → eq s' s
        trn : {s s' s'' : set} → 
              eq s s' → eq s' s'' → eq s s''
open Setoid

record SetoidFun (S S' : Setoid) : Set where
  constructor setoidfun
  field fun : set S → set S'
        feq : {s s' : set S} → 
              eq S s s' → eq S' (fun s) (fun s')
open SetoidFun

SetoidFunEq : {S S' : Setoid}{f g : SetoidFun S S'} →
              fun f ≅ fun g →
              (λ{s}{s'}(p : eq S s s') → feq f p)
              ≅
              (λ{s}{s'}(p : eq S s s') → feq g p) →
              f ≅ g
SetoidFunEq {f = setoidfun fun feq} {setoidfun .fun .feq} refl refl = refl

idFun : {S : Setoid} → SetoidFun S S
idFun = record {fun = id; feq = id}

compFun : {S S' S'' : Setoid} → 
          SetoidFun S' S'' → SetoidFun S S' → SetoidFun S S''
compFun f g = record {fun = fun f ∘ fun g; feq = feq f ∘ feq g}

idl : {X Y : Setoid} {f : SetoidFun X Y} → compFun idFun f ≅ f
idl {f = setoidfun _ _} = refl

idr : {X Y : Setoid} {f : SetoidFun X Y} → compFun f idFun ≅ f
idr {f =  setoidfun _ _} = refl

Setoids : Cat
Setoids = record{
  Obj  = Setoid; 
  Hom  = SetoidFun;
  iden = idFun; 
  comp = compFun; 
  idl  = idl;
  idr  = idr;
  ass  = refl}
-- -}

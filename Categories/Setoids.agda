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

SetoidFunEq : {S S' : Setoid}{f g : set S → set S'} → f ≅ g →
              {feq : {s s' : set S} → eq S s s' → eq S' (f s) (f s')} →
              {geq : {s s' : set S} → eq S s s' → eq S' (g s) (g s')} →
              (∀{s s'}(p : eq S s s') → feq p ≅ geq p) → 
              _≅_ {A = SetoidFun S S'} (setoidfun f feq)
                  {SetoidFun S S'} (setoidfun g geq)
SetoidFunEq {f = f} refl p = cong (setoidfun f) (iext (λ s → iext (λ s' → ext p))) 

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

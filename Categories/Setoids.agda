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
  field fun : set S → set S'
        feq : {s s' : set S} → 
              eq S s s' → eq S' (fun s) (fun s')
open SetoidFun

SetoidFunEq : {S S' : Setoid}{f g : SetoidFun S S'} → fun f ≅ fun g → 
              (∀ s s' → feq f {s}{s'} ≅ feq g {s}{s'}) → f ≅ g
SetoidFunEq {S}{S'} p q = funnycong
  {set S → set S'}
  {λ fun → {s s' : set S} → eq S s s' → eq S' (fun s) (fun s')}
  {SetoidFun S S'} 
  p 
  (iext λ s → iext λ s' → q s s')
  (λ x y → record {fun = x; feq = y}) 

idFun : {S : Setoid} → SetoidFun S S
idFun = record {fun = id; feq = id}

compFun : {S S' S'' : Setoid} → 
          SetoidFun S' S'' → SetoidFun S S' → SetoidFun S S''
compFun f g = record {fun = fun f ∘ fun g; feq = feq f ∘ feq g}

Setoids : Cat
Setoids = record{
  Obj  = Setoid; 
  Hom  = SetoidFun;
  iden = idFun; 
  comp = compFun; 
  idl  = refl;
  idr  = refl;
  ass  = refl}

{-# OPTIONS --type-in-type #-}
module Naturals where

open import Equality
open import Categories
open import Functors

open Cat
open Fun

record NatT {C D}(F G : Fun C D) : Set where
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              comp D (HMap G f) cmp ≅ comp D cmp (HMap F f)

open NatT

NatTEq : {C D : Cat}{F G : Fun C D}{α β : NatT F G} → 
         (λ {X : Obj C} → cmp α {X}) ≅ (λ {X : Obj C} → cmp β {X}) → α ≅ β
NatTEq {C}{D}{F}{G} {α} {β} p = funnyresp 
  {∀ {X} → Hom D (OMap F X) (OMap G X)}
  {λ cmp → ∀{X Y}{f : Hom C X Y} → 
    comp D (HMap G f) cmp ≅ comp D cmp (HMap F f)}
  p
  (iext λ X → iext λ Y → iext λ f → 
    fixtypes (resp (comp D (HMap G f)) (ifresp X p)) 
             (resp (λ (g : Hom D _ _) → comp D g (HMap F f)) (ifresp Y p)))
  λ x y → record{cmp = x;nat = y}

idNat : ∀{C D}{F : Fun C D} → NatT F F
idNat {C}{D}{F} = record {
  cmp = iden D;
  nat = λ{X}{Y}{f} → trans (idr D) (sym (idl D))}

compNat : ∀{C D}{F G H : Fun C D} → NatT G H → NatT F G → NatT F H
compNat {C}{D}{F}{G}{H} α β = record {
  cmp = comp D (cmp α) (cmp β);
  nat = λ{X}{Y}{f} → trans (sym (ass D)) 
                           (trans (resp (λ (f : Hom D (OMap G X) (OMap H Y)) →
                                                comp D f (cmp β)) 
                                        (nat α))
                                  (trans (trans (ass D) 
                                                (resp (comp D (cmp α)) 
                                                      (nat β))) 
                                         (sym (ass D))))}

idlNat : ∀{C D}{F G : Fun C D}{α : NatT F G} → compNat idNat α ≅ α
idlNat {C}{D} = NatTEq (iext λ _ → idl D)

idrNat : ∀{C D}{F G : Fun C D}{α : NatT F G} → compNat α idNat ≅ α
idrNat {C}{D} = NatTEq (iext λ _ → idr D)
 
assNat : ∀{C D}{E F G H : Fun C D}{α : NatT G H}{β : NatT F G}{η : NatT E F} → 
         compNat (compNat α β) η ≅ compNat α (compNat β η)
assNat {C}{D} = NatTEq (iext λ _ → ass D)

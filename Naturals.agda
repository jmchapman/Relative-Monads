module Naturals where

open import Library
open import Categories
open import Functors


open Fun

record NatT {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}(F G : Fun C D) : 
  Set (a ⊔ b ⊔ c ⊔ d) where
  constructor natural
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              comp D (HMap G f) cmp ≅ comp D cmp (HMap F f)

NatTEq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F G : Fun C D}
         {α β : NatT F G} → 
         (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X}) → 
         α ≅ β
NatTEq {α = natural cmp _} {natural .cmp _} refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)

idNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F : Fun C D} → NatT F F
idNat {D = D}{F} = let open Cat D in record {
  cmp = iden;
  nat = λ{X}{Y}{f} → 
    proof
    comp (HMap F f) iden
    ≅⟨ idr ⟩ 
    HMap F f
    ≅⟨ sym idl ⟩ 
    comp iden (HMap F f) ∎} 

compNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F G H : Fun C D} → 
          NatT G H → NatT F G → NatT F H
compNat {D = D}{F}{G}{H} α β = let open Cat D; open NatT in record {
  cmp = comp (cmp α) (cmp β);
  nat = λ{X}{Y}{f} → 
    proof
    comp (HMap H f) (comp (cmp α) (cmp β)) 
    ≅⟨ sym ass ⟩
    comp (comp (HMap H f) (cmp α)) (cmp β)
    ≅⟨ cong (λ f₁ → comp f₁ (cmp β)) (nat α) ⟩
    comp (comp (cmp α) (HMap G f)) (cmp β)
    ≅⟨ ass ⟩
    comp (cmp α) (comp (HMap G f) (cmp β))
    ≅⟨ cong (comp (cmp α)) (nat β) ⟩
    comp (cmp α) (comp (cmp β) (HMap F f))
    ≅⟨ sym ass ⟩
    comp (comp (cmp α) (cmp β)) (HMap F f) 
    ∎}

idlNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F G : Fun C D}
         {α : NatT F G} → compNat idNat α ≅ α
idlNat {D = D} = NatTEq (iext λ _ → Cat.idl D)

idrNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F G : Fun C D}
         {α : NatT F G} → compNat α idNat ≅ α
idrNat {D = D} = NatTEq (iext λ _ → Cat.idr D)
 
assNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{E F G H : Fun C D}
         {α : NatT G H}{β : NatT F G}{η : NatT E F} → 
         compNat (compNat α β) η ≅ compNat α (compNat β η)
assNat {D = D} = NatTEq (iext λ _ → Cat.ass D)

-- Natural isomorphism

record Iso {l m}(C : Cat {l}{m}){A B}(f : Cat.Hom C A B) : Set (l ⊔ m)
  where
  constructor iso
  open Cat C
  field inv  : Hom B A
        rinv : comp f inv ≅ iden {B}
        linv : comp inv f ≅ iden {A}


record NatI {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}(F G : Fun C D) : 
  Set (a ⊔ b ⊔ c ⊔ d) where
  constructor natural
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        cmpI : ∀{X} -> Iso D (cmp {X})
        nat : ∀{X Y}{f : Hom C X Y} → 
              comp D (HMap G f) cmp ≅ comp D cmp (HMap F f)

module Naturals where

open import Library
open import Categories
open import Functors


open Fun

record NatT {a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}(F G : Fun C D) : 
  Set (a ⊔ b ⊔ c ⊔ d) where
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              comp D (HMap G f) cmp ≅ comp D cmp (HMap F f)

open NatT

NatTEq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F G : Fun C D}
         {α β : NatT F G} → 
         (λ {X : Cat.Obj C} → cmp α {X}) ≅ (λ {X : Cat.Obj C} → cmp β {X}) → 
         α ≅ β
NatTEq {C = C}{D = D}{F = F}{G = G}{α = α}{β = β} p = let open Cat in funnycong
  {A = ∀ {X} → Hom D (OMap F X) (OMap G X)}
  {B = λ cmp → ∀{X Y}{f : Hom C X Y} → 
    comp D (HMap G f) cmp ≅ comp D cmp (HMap F f)}
  (proof 
   (λ {X} → cmp α {X}) 
   ≅⟨ p ⟩ 
   (λ {X} → cmp β {X}) 
   ∎)
  (iext λ X → iext λ Y → iext λ f → 
    fixtypes (cong (comp D (HMap G f)) (ifcong X p)))
  λ x y → record{cmp = x;nat = y}

idNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F : Fun C D} → NatT F F
idNat {C = C}{D = D}{F = F} = let open Cat D in record {
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
compNat {C = C}{D = D}{F = F}{G = G}{H = H} α β = let open Cat D in record {
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
idlNat {C = C}{D = D} = NatTEq (iext λ _ → Cat.idl D)

idrNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{F G : Fun C D}
         {α : NatT F G} → compNat α idNat ≅ α
idrNat {C = C}{D = D} = NatTEq (iext λ _ → Cat.idr D)
 
assNat : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}}{E F G H : Fun C D}
         {α : NatT G H}{β : NatT F G}{η : NatT E F} → 
         compNat (compNat α β) η ≅ compNat α (compNat β η)
assNat {C = C}{D = D} = NatTEq (iext λ _ → Cat.ass D)

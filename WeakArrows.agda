module WeakArrows where

open import Library
open import Categories

record Arrow {l m}(J : Cat {l}{m}) : Set (lsuc (l ⊔ m)) where
  constructor arrow
  open Cat J
  field R      : Obj → Obj → Set m
        pure   : ∀{X Y} -> Hom X Y -> R X Y
        _<<<_  : ∀{X Y Z} → R Y Z -> R X Y -> R X Z
        alaw1  : ∀{X Y Z}(g : Hom Y Z)(f : Hom X Y) ->
                 pure (comp g f) ≅ pure g <<< pure f
        alaw2  : ∀{X Y}(s : R X Y) -> s <<< pure iden ≅ s
        alaw3  : ∀{X Y}(r : R X Y) -> pure iden <<< r ≅ r
        alaw4  : ∀{W X Y Z}(t : R Y Z)(s : R X Y)(r : R W X) ->
                 t <<< (s <<< r) ≅ (t <<< s) <<< r

open import Functors
open import Naturals
open import Categories.Sets
open import YonedaLemma
open import RMonads

module Arrow2RMonad {l m}(C : Cat {l}{m})(A : Arrow C) where
  open Cat C
  open Arrow A
  
  T : Cat.Obj C -> Fun (C Op) (Sets {m})
  T X = functor
    (λ Y -> R Y X)
    (λ f s -> s <<< pure f)
    (ext alaw2)
    (ext (λ s -> trans (cong (s <<<_) (alaw1 _ _)) (alaw4 _ _ _)))

  η : {X : Obj} -> NatT HomF[-, X ] (T X)
  η = natural pure (ext λ _ -> sym (alaw1 _ _))

  bind : {X Y : Obj} ->
         NatT HomF[-, X ] (T Y) -> NatT (T X) (T Y)
  bind α = natural (λ s -> cmp iden <<< s) (ext λ _ -> sym (alaw4 _ _ _))
    where open NatT α
  -- cmp iden is one direction of the yoneda lemma

  law1 : {X : Obj} → bind (η {X}) ≅ idNat {F = T X}
  law1 = NatTEq (iext (\ _ -> ext alaw3))

  law2 : {X Y : Obj}{f : NatT HomF[-, X ] (T Y)} → 
         compNat (bind f) η ≅ f
  law2 {f = f} = NatTEq
    (iext \ _ -> ext \ s -> trans (fcong iden (nat {f = s})) (cong cmp idl))
    where open NatT f

  law3 : {X Y Z : Obj}
         {f : NatT HomF[-, X ] (T Y)} → 
         {g : NatT HomF[-, Y ] (T Z)} →
         bind (compNat (bind g) f) ≅ compNat (bind g) (bind f)
  law3 = NatTEq (iext \ W -> ext (\ s -> sym (alaw4 _ _ s)))

  ArrowRMonad : RMonad (y C)
  ArrowRMonad = rmonad
    T
    η
    bind
    law1
    law2
    (λ {_ _ _ f g} -> law3 {f = f}{g = g})

module RMonad2Arrow {l m}(C : Cat {l}{m})(M : RMonad (y C)) where
  open Cat C
  open RMonad M
  open Fun
  open NatT

  R : Obj → Obj → Set m
  R X Y = OMap (T Y) X

  pure : {X Y : Obj} → Hom X Y → R X Y
  pure f = cmp η f

  _<<<_ : ∀{X Y Z} → R Y Z → R X Y → R X Z
  s <<< t = cmp (bind (ylem C (T _) _ s)) t

  alaw1 : ∀{X Y Z}(g : Hom Y Z)(f : Hom X Y) →
          pure (comp g f) ≅ (pure g <<< pure f)
  alaw1 g f = trans
    (sym (fcong g (nat η)))
    (sym (fcong f (ifcong _ (cong cmp law2))))

  alaw2 : ∀{X Y} -> (s : R X Y) → (s <<< pure iden) ≅ s
  alaw2 s = trans
    (fcong iden (ifcong _ (cong cmp law2)))
    (fcong s (fid (T _)))

  alaw3 : ∀{X Y}(r : R X Y) → (pure iden <<< r) ≅ r
  alaw3 r = trans
    (cong (\ α -> cmp (bind α) r)
          (NatTEq (iext \ Z -> ext \ f -> trans
            (fcong iden (nat η))
            (cong (cmp η) idl))))
    (fcong r (ifcong _ (cong cmp law1)))

  alaw4 : ∀{W X Y Z}(t : R Y Z)(s : R X Y)(r : R W X) →
          (t <<< (s <<< r)) ≅ ((t <<< s) <<< r)
  alaw4 t s r = trans
    (sym (fcong r (ifcong _ (cong cmp law3))))
    (cong (\ α -> cmp (bind α) r)
          (NatTEq (iext \ _ -> ext \ _ ->
            sym (fcong s (nat (bind (ylem C (T _) _ t)))))))

  RMonadArrow : Arrow C
  RMonadArrow = arrow
    R
    pure
    _<<<_
    alaw1
    alaw2
    alaw3
    alaw4

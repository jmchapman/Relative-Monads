module YonedaLemma where

open import Library
open import Categories
open import Categories.Sets
open import Functors
open import Naturals
open import FunctorCat

HomF[-,_] : ∀{l m}{C : Cat {l}{m}}(X : Cat.Obj C) -> Fun (C Op) (Sets {m})
HomF[-,_] {C = C} B = functor
  (\ X -> Hom X B)
  (\ f g -> comp g f)
  (ext \ _ -> idr)
  (ext \ _ -> sym ass)
  where open Cat C

HomN[-,_] : ∀{l m}{C : Cat {l}{m}}{X Y : Cat.Obj C}(f : Cat.Hom C X Y) ->
            NatT (HomF[-,_] {C = C} X) HomF[-, Y ]
HomN[-,_] {C = C} f = natural
  (comp f)
  (ext \ _ -> ass)
  where open Cat C

y : ∀{l m}(C : Cat {l}{m}) -> Fun C (FunctorCat (C Op) (Sets {m}))
y C = functor
  HomF[-,_]
  HomN[-,_]
  (NatTEq (iext \ _ -> ext \ _ -> idl))
  (NatTEq (iext \ _ -> ext \ _ -> ass))
  where open Cat C

yleminv : ∀{l m}(C : Cat {l}{m})(F : Fun (C Op) (Sets {m}))(X : Cat.Obj C) ->
          NatT (Fun.OMap (y C) X) F -> Fun.OMap F X
yleminv C F X α = NatT.cmp α {X} (Cat.iden C)

ylem : ∀{l m}(C : Cat {l}{m})(F : Fun (C Op) (Sets {m}))(X : Cat.Obj C) ->
       Fun.OMap F X -> NatT (Fun.OMap (y C) X) F
ylem C F X FX = natural
  (\ {X'} f -> HMap f FX)
  (\{X'}{Y}{f} -> ext \ g -> sym (fcong FX (fcomp {f = f}{g = g})) ) 
  where open Cat C; open Fun F

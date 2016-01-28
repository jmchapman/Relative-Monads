module DayConvolution where

open import Library
open import Functors
open import Categories
open import Categories.Sets
open import MonoidalCat

-- first draft

ODay : ∀{l m}(M : Monoidal {l}{m})
       (F G : Fun (Monoidal.C M) (Sets {l})) ->
       Cat.Obj (Monoidal.C M) -> Set _
ODay M F G X =
  Σ Obj \Y -> Σ Obj \Z -> OMap F Y × OMap G Z × Hom X (OMap ⊗ (Y , Z))
  where open Monoidal M; open Cat C; open Fun

HDay : ∀{l m}(M : Monoidal {l}{m})
       (F G : Fun (Monoidal.C M) (Sets {l})) -> ∀{X X'} ->
       Cat.Hom (Monoidal.C M) X X' -> ODay M F G X' -> ODay M F G X
HDay M F G f (y , z , fy , gz , g) = y , z , fy , gz , comp g f
  where open Monoidal M; open Cat C


DayF : ∀{l m}(M : Monoidal {l}{m})
       (F G : Fun (Monoidal.C M) (Sets {l})) -> Fun ((Monoidal.C M) Op) Sets
DayF M F G = functor
  (ODay M F G)
  (HDay M F G)
  (\ {X} -> ext (\{ (y , z , fy , gz , g) ->
    cong (λ g → y , z , fy , gz , g) idr}))
  (\ {X Y Z h k} -> ext (\{ (y , z , fy , gz , g) ->
    cong (λ l → y , z , fy , gz , l) (sym ass)}))
  where open Monoidal M; open Cat C
  
-- subject to some additional conditions
-- forall h : y -> y'.
--   (y , F h fy' , gz , g) ~ (y' , z , fy' , gz , [h,id] . g)
--
-- forall k : z -> z'
--   (y , z , fy , G k gz' , g) ~ (y , z' , fy , gz' , [id,k] . g)


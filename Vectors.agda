record SemiRing : Set1 where
  field
    R    : Set
    _+_  : R -> R -> R
    zero : R
    _*_  : R -> R -> R
    one  : R

module Vectors (S : SemiRing) where

  open SemiRing S
  open import Data.Nat renaming (ℕ to Nat; zero to z; _*_ to times; _+_ to plus)
  open import Data.Fin renaming (zero to z) hiding (_+_)
  open import RMonads
  open import Functors.Fin 
  open import Data.Bool
  open import Function
  open import Relation.Binary.HeterogeneousEquality

  Vec : Nat -> Set
  Vec n = Fin n -> R

  Matrix : Nat -> Nat -> Set
  Matrix m n = Fin m -> Vec n

  -- unit
  delta : forall {n} -> Matrix n n
  delta i j = if feq i j then one else zero 

  transpose : forall {m n} -> Matrix m n -> Matrix n m
  transpose A = λ j i -> A i j

  dot : forall {n} -> Vec n -> Vec n -> R
  dot {z}     x y = zero
  dot {suc n} x y = (x z * y z) + dot (x ∘ suc) (y ∘ suc)
  
  mult : forall {m n} -> Matrix m n -> Vec m -> Vec n
  mult A x = λ j -> dot (transpose A j) x

  VecRMon : RMonad FinF
  VecRMon = rmonad
    Vec
    delta
    mult
    {!!}
    {!!}
    {!!}



    where
{-
    lem : forall {n}(x : Vec n)(j : Fin n) -> dot (λ i → if feq i j then one else zero) x ≅ x j
    lem {z} x ()
    lem {suc n} x z = {!lem {n} (x ∘ suc) !}
    lem {suc n} x (suc j) = {!!}

 -}

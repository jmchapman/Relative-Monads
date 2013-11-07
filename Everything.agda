module Everything where 

-- basic utilities
open import Equality
open import Fin
open import Isomorphism
open import Setoids -- should be replaced by standard libary def

-- basic category theory
open import Categories
open import Functors
open import FullyFaithful
open import Naturals
open import Sets
open import Families
open import Initial
open import Terminal

-- basic examples
open import Monoids
open import FunctorCat

-- ordinary monads
open import Monads2
open import MonadMorphs2
open import Adjunctions2
open import Adj2Mon2
open import Kleisli2
open import KleisliFunctors2
open import KleisliAdj2
open import EM2
open import EMFunctors2
open import EMAdj2
open import CatofAdj2
open import InitAdj2
open import TermAdj2Obj
open import TermAdj2Hom
open import TermAdj2Uniq
open import TermAdj2

-- relative monads
open import RMonads2
open import RMonadMorphs2
open import RAdjunctions2
open import RAdj2RMon2
open import REM2
open import REMFunctors2
open import REMAdj2
open import RKleisli2
open import RKleisliFunctors2
open import RKleisliAdj2
open import Restriction
open import SpecialCase
open import CatofRAdj2
open import InitRAdj2

-- rmonad examples
open import WellScopedTerms
open import WellScopedTermsModel
open import WellTypedTerms3
open import WellTypedTermsModel3

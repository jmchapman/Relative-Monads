module Everything where 

-- basic utilities
open import Equality
open import Isomorphism


-- basic category theory
open import Categories
open import Categories.Sets
open import Categories.Families
open import Categories.Initial
open import Categories.Terminal
open import Categories.Setoids -- should be replaced by standard libary def

open import Functors
open import Functors.Fin
open import Functors.FullyFaithful

open import Naturals

-- basic examples
open import Monoids
open import FunctorCat

-- ordinary monads
open import Monads
open import MonadMorphs
open import Adjunctions
open import Adj2Mon
open import Kleisli
open import Kleisli.Functors
open import Kleisli.Adjunction
open import EM
open import EM.Functors
open import EM.Adjunction
open import CatofAdj
open import InitAdj
open import TermAdjObj
open import TermAdjHom
open import TermAdjUniq
open import TermAdj

-- relative monads
open import RMonads
open import RMonadMorphs
open import RAdjunctions
open import RAdj2RMon
open import REM
open import REMFunctors
open import REMAdj
open import RKleisli
open import RKleisliFunctors
open import RKleisliAdj
open import Restriction
open import SpecialCase
open import CatofRAdj
open import InitRAdj
open import TermRAdjObj
open import TermRAdjHom
open import TermRAdj

-- rmonad examples
open import WellScopedTerms
open import WellScopedTermsModel
open import WellTypedTerms
open import WellTypedTermsModel

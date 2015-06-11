module Everything where 

-- basic utilities
open import Library
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
open import Monads.MonadMorphs
open import Adjunctions
open import Adjunctions.Adj2Mon
open import Monads.Kleisli
open import Monads.Kleisli.Functors
open import Monads.Kleisli.Adjunction
open import Monads.EM
open import Monads.EM.Functors
open import Monads.EM.Adjunction
open import Monads.CatofAdj
open import Monads.CatofAdj.InitAdj
open import Monads.CatofAdj.TermAdjObj
open import Monads.CatofAdj.TermAdjHom
open import Monads.CatofAdj.TermAdjUniq
open import Monads.CatofAdj.TermAdj

-- relative monads
open import RMonads
open import RMonads.RMonadMorphs
open import RAdjunctions
open import RAdjunctions.RAdj2RMon
open import RMonads.REM
open import RMonads.REM.Functors
open import RMonads.REM.Adjunction
open import RMonads.RKleisli
open import RMonads.RKleisli.Functors
open import RMonads.RKleisli.Adjunction
open import RMonads.Restriction
open import RMonads.SpecialCase
open import RMonads.CatofRAdj
open import RMonads.CatofRAdj.InitRAdj
open import RMonads.CatofRAdj.TermRAdjObj
open import RMonads.CatofRAdj.TermRAdjHom
open import RMonads.CatofRAdj.TermRAdj
 
-- rmonad examples
open import WellScopedTerms
open import WellScopedTermsModel
open import WellTypedTerms
open import WellTypedTermsModel

This repository contains a formalisation of relative monads. Monads
are relative monads on the identity functor so it is not technically
necessary to repeat the same constructions for ordinary
monads. Nevertheless I include separate implementations of ordinary
monads and related constructions as a warmup.

Most of the code is quite polished. The stuff related to categories of
adjunctions is still pretty gory.

Basic category theory
---------------------
Categories
Initial object
Terminal object
CoProducts
Functors
Full and Faithfulness
Natural Transformations
Day Convolution
Yoneda Lemma

Relative monad theory
---------------------
(Rel.) Monads
(Rel.) Adjunctions
(Rel.) Kleisli Category
(Rel.) Kleisli Adjunction
(Rel.) EM Category
(Rel.) EM Adjunction
(Rel.) Modules
Category of (Rel.) Adjunctions for a (Relative) Monad
Proof that (Rel.) Kleisli is the Initial Object in the Cat. of (Rel.) Adjs.
Proof that (Rel.) EM is the Terminal Object in the Cat. of (Rel.) Adjs.

Examples
--------
Proof that Well-Scoped Lambda Terms are a Rel. Monad.
Proof that a Lambda-Model is a Rel. EM Algebra.
Proof that Well-Typed Lambda Terms are a Rel. Monad.
Proof that an evaluator for Well-Typed Lambda Terms is a Rel. EM Algebra.
Proof that weak arrows are relative monads on Yoneda
Proof that Rel. Monads on Fin are Lawvere theories
Proof that Algebras for Rel. Monads on Fin are models of Lawvere theories.
Proof that vector spaces are Rel. Monads
Proof that left-modules are algebras of Rel. Monads
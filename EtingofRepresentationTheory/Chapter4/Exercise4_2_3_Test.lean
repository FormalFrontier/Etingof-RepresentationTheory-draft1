import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_Assembly
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_Cocenter

/-!
# Downstream import/`#check` test for Exercise 4.2.3

This file imports the Exercise 4.2.3 chain and pins the public signatures of the
modular irreducible-count results. Its purpose is to catch a regression in the
*source* of Exercise 4.2.3 even when cached oleans would otherwise hide it from the
aggregate build: because this file `import`s the endpoints and re-elaborates their
statements (and applies them), it forces a fresh check of the public API.

See issue #7535 (restore the modular irreducible-count chain for Exercise 4.2.3).
-/

open CategoryTheory

-- The public endpoints must remain importable under these names.
#check @Etingof.Exercise4_2_3
#check @Etingof.not_isSemisimpleRing_of_card_eq_zero
#check @Etingof.CocenterMonoidAlgebra.classCoeff
#check @Etingof.CocenterMonoidAlgebra.classCoeff_mul_comm

-- The strict-count endpoint: no `sorry` may leak in.
#print axioms Etingof.Exercise4_2_3

-- Signature lock and application test for the strict count. When `|G| = 0` in `k`,
-- the number of isomorphism classes of irreducibles is strictly less than the number
-- of conjugacy classes. Applying it forces a fresh elaboration of the conclusion's
-- shape; any drift in the hypotheses or conclusion makes this `example` fail.
example (k G : Type) [Field k] [Group G] [Fintype G]
    (h : (Fintype.card G : k) = 0) :
    Nat.card (Etingof.IrrepClasses k G) < Nat.card (ConjClasses G) :=
  Etingof.Exercise4_2_3 k G h

-- Non-semisimplicity in the modular case: the group algebra is not semisimple.
example (k G : Type) [Field k] [Group G] [Fintype G]
    (h : (Fintype.card G : k) = 0) :
    ¬ IsSemisimpleRing (MonoidAlgebra k G) :=
  Etingof.not_isSemisimpleRing_of_card_eq_zero h

-- The cocenter trace-form ingredient: the class-coefficient map is a trace.
open Etingof.CocenterMonoidAlgebra in
example (k G : Type) [Field k] [Group G] [Fintype G] [DecidableEq G]
    (x y : MonoidAlgebra k G) :
    classCoeff k G (x * y) = classCoeff k G (y * x) :=
  classCoeff_mul_comm x y

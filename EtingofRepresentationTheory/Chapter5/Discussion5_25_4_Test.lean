import EtingofRepresentationTheory.Chapter5.Discussion5_25_4

/-!
# Downstream import/`#check` test for Discussion 5.25.4

This file imports `Chapter5/Discussion5_25_4.lean` and pins the public signatures of the
complementary-series orbit-count endpoints. Its purpose is to catch a regression in the
source of Discussion 5.25.4 even when cached oleans would otherwise hide it from the
aggregate build: because this file `import`s the source and re-elaborates the endpoint
statements, it forces a fresh check of their public API.

See issue #7508 (restore the complementary-series construction in Discussion 5.25.4).
-/

open Etingof.ComplementarySeries

-- The public endpoints must remain importable under these names.
#check @Etingof.ComplementarySeries.cs_f
#check @Etingof.ComplementarySeries.cs_moved
#check @Etingof.ComplementarySeries.cs_reps
#check @Etingof.ComplementarySeries.cs_f_involutive
#check @Etingof.ComplementarySeries.cs_moved_card
#check @Etingof.ComplementarySeries.cs_reps_transversal
#check @Etingof.ComplementarySeries.cs_reps_card

-- Signature locks: each `example` fails to elaborate if the corresponding statement drifts.

/-- Involution: the Frobenius map `ν ↦ ν^q` (multiplication by `q`) squares to the identity. -/
example (q : ℕ) (hq : 2 ≤ q) (x : ZMod (q ^ 2 - 1)) : cs_f q (cs_f q x) = x :=
  cs_f_involutive q hq x

/-- Moved-set count: exactly `q (q − 1)` characters satisfy `ν^q ≠ ν`. -/
example (q : ℕ) [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) : (cs_moved q).card = q * (q - 1) :=
  cs_moved_card q hq

/-- Transversal: the involution pairs the moved set into two-element orbits, with
`cs_reps q` a one-per-orbit transversal. -/
example (q : ℕ) [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    Disjoint (cs_reps q) ((cs_reps q).image (cs_f q))
      ∧ (cs_reps q) ∪ (cs_reps q).image (cs_f q) = cs_moved q
      ∧ ((cs_reps q).image (cs_f q)).card = (cs_reps q).card :=
  cs_reps_transversal q hq

/-- The count: the number of complementary-series representations is `½ q (q − 1)`. -/
example (q : ℕ) [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    (cs_reps q).card = q * (q - 1) / 2 :=
  cs_reps_card q hq

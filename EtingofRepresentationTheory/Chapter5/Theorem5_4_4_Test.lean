import EtingofRepresentationTheory.Chapter5.Theorem5_4_4

/-!
# Downstream import/`#check` test for Theorem 5.4.4

This file imports `Chapter5/Theorem5_4_4.lean` and pins the public signature of the
coprimality character-vanishing / scalar-action theorem. Its purpose is to catch a
regression in the source of Theorem 5.4.4 even when cached oleans would otherwise hide
it from the aggregate build: because this file `import`s the theorem file and
re-elaborates the endpoint statement, it forces a fresh check of its public API.

See issue #7514 (restore fresh-buildable Theorem 5.4.4).
-/

open CategoryTheory

-- The public endpoint must remain importable under this name.
#check @Etingof.Theorem5_4_4

-- Signature lock and application test.  For a simple `V` and `g` whose conjugacy-class
-- size is coprime to `dim V`, the theorem must deliver the character-vanishing /
-- scalar-action dichotomy.  Applying it and destructuring both branches forces a fresh
-- elaboration of the conclusion's shape; any drift in the hypotheses or conclusion makes
-- this `example` fail to elaborate.
example (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V] (g : G)
    (h_coprime : Nat.Coprime
      (Fintype.card { h : G // IsConj g h })
      (Module.finrank ℂ V)) :
    True := by
  rcases Etingof.Theorem5_4_4 G V g h_coprime with _hvanish | ⟨_c, _hscalar⟩
  · trivial
  · trivial

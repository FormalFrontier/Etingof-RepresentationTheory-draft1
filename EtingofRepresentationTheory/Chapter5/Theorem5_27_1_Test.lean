import EtingofRepresentationTheory.Chapter5.Theorem5_27_1

/-!
# Downstream import/`#check` test for Theorem 5.27.1

This file imports `Chapter5/Theorem5_27_1.lean` and pins the public signatures of the
semidirect-product classification and its base-point-independence engine. Its purpose is
to catch a regression in the source of Theorem 5.27.1 even when cached oleans would
otherwise hide it from the aggregate build: because this file `import`s the theorem file
and re-elaborates the endpoint statements, it forces a fresh check of their public API.

See issue #7507 (restore fresh-buildable Theorem 5.27.1 semidirect-product classification).
-/

-- The public classification endpoint and the base-point-independence engine must remain
-- importable under these names.
#check @Etingof.Theorem5_27_1
#check @Etingof.inducedRepV_basepoint_independent

-- Signature lock for the full classification endpoint.  The anonymous destructuring pins
-- the shape of the packaged data (`dualSmul`, `stab`, `V`, `transport`) together with all
-- nine conjuncts: irreducibility, the orbit/transport classification, completeness, the
-- character and dimension formulas, functoriality, base-point independence (`_hBase`),
-- central-transport triviality, and transport-preserves-simplicity.  Any drift in the
-- endpoint's structure makes this `example` fail to elaborate.
example (G A : Type) [Group G] [CommGroup A] [Fintype G] [Fintype A] (φ : G →* MulAut A) :
    True := by
  obtain ⟨_dualSmul, _hdual, _stab, _hstab, _V, _transport,
      _hIrr, _hClass, _hComplete, _hChar, _hDim, _hFunct, _hBase, _hCentral, _hSimp⟩ :=
    Etingof.Theorem5_27_1 G A φ
  trivial

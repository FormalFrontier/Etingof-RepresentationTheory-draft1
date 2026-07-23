import EtingofRepresentationTheory.Chapter5.Corollary5_12_4

/-!
# Downstream import/`#check` test for Corollary 5.12.4

This file imports `Chapter5/Corollary5_12_4.lean` and pins the public signatures of the
rational-form results. Its purpose is to catch a regression in the source of Corollary
5.12.4 even when cached oleans would otherwise hide it from the aggregate build: because
this file `import`s the corollary file and re-elaborates the endpoint statements, it forces
a fresh check of their public API.

See issue #7522 (restore fresh-buildable rational-form Corollary 5.12.4).
-/

-- The public endpoints must remain importable under these names.
#check @Etingof.SpechtModule_complexification
#check @Etingof.Corollary5_12_4

open scoped TensorProduct

-- Signature lock and application test for the complexification isomorphism. Applying it
-- and destructuring the witness forces a fresh elaboration of the `ℂ`-linear equivalence
-- `ℂ ⊗_ℚ V_λ^ℚ ≃ V_λ` and its `Sₙ`-equivariance clause; any drift makes this fail.
example (n : ℕ) (la : Nat.Partition n) :
    True := by
  obtain ⟨_e, _hequiv⟩ := Etingof.SpechtModule_complexification n la
  trivial

-- Signature lock and application test for the corollary. Given a simple `ℂ[Sₙ]`-module,
-- the theorem must produce a partition together with the classification isomorphism, the
-- simplicity of the rational Specht module, and the complexification equivalence.
example (n : ℕ) (M : Type)
    [AddCommGroup M] [Module (Etingof.SymGroupAlgebra n) M]
    [IsSimpleModule (Etingof.SymGroupAlgebra n) M] :
    True := by
  obtain ⟨_la, _hclass, _hsimple, _e, _hequiv⟩ := Etingof.Corollary5_12_4 n M
  trivial

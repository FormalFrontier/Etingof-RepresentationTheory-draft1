import EtingofRepresentationTheory.Chapter5.Theorem5_26_1

/-!
# Downstream import/`#check` test for Theorem 5.26.1 (Artin's theorem)

This file imports `Chapter5/Theorem5_26_1.lean` and pins the public signature of the
Artin element-coverage / rational character-span equivalence. Its purpose is to catch a
regression in the source of Theorem 5.26.1 even when cached oleans would otherwise hide
it from the aggregate build: because this file `import`s the theorem file and
re-elaborates the endpoint statement, it forces a fresh check of its public API.

See issue #7513 (restore fresh-buildable Artin theorem and correct its stale metadata).
-/

-- The public endpoint must remain importable under this name.
#check @Etingof.Theorem5_26_1

-- Signature lock and application test.  For a conjugation-invariant system `X`, the
-- theorem must deliver the equivalence between `X` covering `G` and every irreducible
-- character lying in the ℚ-span of induced characters from subgroups in `X`.  Consuming
-- both directions forces a fresh elaboration of the hypotheses and conclusion shape; any
-- drift makes this `example` fail to elaborate.
example (G : Type) [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X)
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H) :
    ∀ (V : FDRep ℂ G), CategoryTheory.Simple V →
      V.character ∈ Submodule.span ℚ
        {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
          f = Etingof.inducedCharacter H W.character} :=
  (Etingof.Theorem5_26_1 G X hX).mp hcov

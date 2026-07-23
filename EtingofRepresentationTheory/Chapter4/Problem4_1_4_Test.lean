import EtingofRepresentationTheory.Chapter4.Problem4_1_4

/-!
# Downstream import/`#check` test for Problem 4.1.4

This file imports `Chapter4/Problem4_1_4.lean` and pins the public signature of the
theorem that every irreducible representation of a `p`-group over a field of
characteristic `p` is trivial. Its purpose is to catch a regression in the source of
Problem 4.1.4 even when cached oleans would otherwise hide it from the aggregate build:
because this file `import`s the theorem file and re-elaborates the endpoint statement, it
forces a fresh check of its public API.

See issue #7536 (restore fresh-buildable Problem 4.1.4).
-/

-- The public endpoint must remain importable under this name.
#check @Etingof.Problem4_1_4

-- Signature lock and application test.  For a group `G` of order `p ^ n` acting
-- irreducibly on `V` over a field `k` of characteristic `p`, the theorem must yield that
-- every group element acts as the identity operator.  Applying it forces a fresh
-- elaboration of the conclusion's shape; any drift in the hypotheses or conclusion makes
-- this `example` fail to elaborate.
example {p n : ℕ} [Fact p.Prime]
    {k : Type} [Field k] [CharP k p]
    {G : Type} [Group G] [Fintype G] (hG : Fintype.card G = p ^ n)
    {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    (hV : IsSimpleModule (MonoidAlgebra k G) ρ.asModule)
    (g : G) :
    ρ g = LinearMap.id :=
  Etingof.Problem4_1_4 hG ρ hV g

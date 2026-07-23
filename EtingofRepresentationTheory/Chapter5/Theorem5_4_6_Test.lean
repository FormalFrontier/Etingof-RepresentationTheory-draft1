import EtingofRepresentationTheory.Chapter5.Theorem5_4_6

/-!
# Downstream import/`#check` test for Theorem 5.4.6

This file imports `Chapter5/Theorem5_4_6.lean` and pins the public signature of the
prime-power conjugacy-class nonsimplicity theorem. Its purpose is to catch a regression
in the source of Theorem 5.4.6 even when cached oleans would otherwise hide it from the
aggregate build: because this file `import`s the theorem file and re-elaborates the
endpoint statement, it forces a fresh check of its public API.

See issue #7515 (restore fresh-buildable Theorem 5.4.6).
-/

-- The public endpoint must remain importable under this name.
#check @Etingof.Theorem5_4_6

-- Signature lock and application test.  If `G` has a conjugacy class of size `p ^ k`
-- with `p` prime and `k > 0`, the theorem must produce a proper nontrivial normal
-- subgroup.  Applying it and destructuring the witness forces a fresh elaboration of the
-- conclusion's shape; any drift in the hypotheses or conclusion makes this `example` fail
-- to elaborate.
example (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) (g : G)
    (hconj : Fintype.card { h : G // IsConj g h } = p ^ k) :
    True := by
  obtain ⟨_N, _hnormal, _hbot, _htop⟩ := Etingof.Theorem5_4_6 G p hp k hk g hconj
  trivial

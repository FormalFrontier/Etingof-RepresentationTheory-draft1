import EtingofRepresentationTheory.Chapter5.Theorem5_25_2

/-!
# Downstream import/`#check` test for the principal-series dimension endpoint

This file imports `Chapter5/Theorem5_25_2.lean` and pins the public signature of the
principal-series dimension endpoint `Etingof.GL2.principalSeries_finrank`. Its purpose is
twofold:

* it demonstrates that a *client* can state and use `dim V(χ₁, χ₂) = q + 1` through the
  normal Chapter 5 API, without reaching into the private `principalSeriesSubmodule`
  namespace where the underlying computation lives; and
* because it `import`s the source and re-elaborates the endpoint statement, it forces a
  fresh check of the public API even when cached oleans would otherwise hide a source
  regression from the aggregate build.

See issue #7563 (expose the principal-series dimension `q + 1`).
-/

open Etingof.GL2

-- The public endpoint must remain importable under this name.
#check @Etingof.GL2.principalSeries_finrank

/-- Signature lock: a client obtains `dim V(χ₁, χ₂) = q + 1` for `q = p ^ n` from the
public API alone. This `example` fails to elaborate if the statement drifts. -/
example (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero n]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ (principalSeries p n chi1 chi2).V = p ^ n + 1 :=
  principalSeries_finrank p n chi1 chi2

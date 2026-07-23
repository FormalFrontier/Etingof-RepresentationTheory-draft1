import EtingofRepresentationTheory.Chapter5.GL2ConjugacyClassCount

/-!
# Downstream import/`#check` test for the Discussion 5.25.1 class-data endpoints

This file imports `Chapter5/GL2ConjugacyClassCount.lean` and pins the public
signatures of the per-type **centralizer-order** and **conjugacy-class-size**
endpoints of Etingof's §5.25 table. Its purpose is twofold:

* it demonstrates that a *client* can read off each table column
  (`|C_G(g)|` and `|class of g|`) through the public `GL2` API, without reaching
  into the private `centralizerCard_parabolic` / `centralizerCard_splitSemisimple`
  / `centralizerCard_elliptic` proof helpers where the underlying counts live; and
* because it `import`s the source and re-elaborates each endpoint statement, it
  forces a fresh check of the public API even when cached oleans would otherwise
  hide a source regression from the aggregate build.

See issue #7500 (expose the representative, centralizer, and class-size columns
of the GL₂ conjugacy table).
-/

-- Orbit–stabilizer bridge relating class size and centralizer order.
#check @GL2.orbit_card_mul_centralizerCard

-- Centralizer-order column (scalar / parabolic / split-semisimple / elliptic).
#check @GL2.centralizerCard_isScalar
#check @GL2.centralizerCard_isParabolic
#check @GL2.centralizerCard_isSplitSemisimple
#check @GL2.centralizerCard_isElliptic

-- Conjugacy-class-size column (# elements per class).
#check @GL2.classCard_isScalar
#check @GL2.classCard_isParabolic
#check @GL2.classCard_isSplitSemisimple
#check @GL2.classCard_isElliptic

variable {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
  [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)]
  [Fintype (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))]

/-- Signature lock: a client obtains the parabolic centralizer order `q(q−1)`
from the public API alone. -/
example {g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)}
    (hg : GL2.IsParabolic g) :
    Nat.card (Subgroup.centralizer ({g} : Set _))
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) :=
  GL2.centralizerCard_isParabolic hg

/-- Signature lock: a client obtains the elliptic conjugacy-class size `q² − q`,
phrased as the cardinality of the orbit under conjugation. -/
example (hn : n ≠ 0) {g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)}
    (hg : GL2.IsElliptic g) :
    Nat.card (MulAction.orbit (ConjAct (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))) g)
      = Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n) :=
  GL2.classCard_isElliptic hn hg

/-- Signature lock: a scalar element has a singleton conjugacy class. -/
example {g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)}
    (hg : GL2.IsScalar g) :
    Nat.card (MulAction.orbit (ConjAct (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))) g)
      = 1 :=
  GL2.classCard_isScalar hg

import Mathlib
import EtingofRepresentationTheory.Chapter5.GL2CharacterValues

/-!
# Number of conjugacy classes per type in GL₂(𝔽_q)  (Discussion 5.25.1)

Etingof's table in §5.25 lists, alongside the number of *elements* in each
conjugacy class, the number of *classes* of each type:

| Type              | # classes            |
|-------------------|----------------------|
| scalar            | `q − 1`              |
| parabolic         | `q − 1`              |
| split semisimple  | `(q−1)(q−2)/2`       |
| elliptic          | `q(q−1)/2`           |
| total             | `q² − 1`             |

The element counts are `GL2.card_isScalar`, `GL2.card_isParabolic`,
`GL2.card_isSplitSemisimple`, `GL2.card_isElliptic` in `GL2ConjugacyClasses`;
each counts how many *matrices* of the given type there are. Here we instead
count the *conjugacy classes* themselves, by pushing each type's element set
through the quotient map `ConjClasses.mk` and taking the cardinality of the
image. This is the first instantiation of `ConjClasses` for GL₂ in the project.

## What is proved here

* The four type predicates (`GL2.IsScalar`, `GL2.IsParabolic`,
  `GL2.IsSplitSemisimple`, `GL2.IsElliptic`) are **conjugation-invariant**
  (`GL2.isScalar_conj_iff`, `GL2.isParabolic_conj_iff`, etc.). This is what
  makes "the type of a conjugacy class" well defined, and is proved fully from
  `Etingof.disc_conj_eq` (discriminant is a class function) together with the
  centrality of scalar matrices.
* The **scalar count** `GL2.numScalarClasses = q − 1` is proved fully: each
  scalar matrix is central, so its conjugacy class is a singleton and
  `ConjClasses.mk` is injective on the scalar set; the count therefore equals
  the number of scalar *elements*, which is `q − 1` by `GL2.card_isScalar`.

## What is deferred (top-down `sorry`s, with the book's argument recorded)

The parabolic / split-semisimple / elliptic counts and the grand total `q² − 1`
are stated but their proofs are deferred. Each follows the book by dividing the
element count of a type by the (constant) size of a class of that type:

* parabolic:        `(q−1)(q²−1) / (q²−1)      = q−1`
* split semisimple: `(q−1)(q−2)q(q+1)/2 / (q²+q) = (q−1)(q−2)/2`
* elliptic:         `q²(q−1)²/2 / (q²−q)         = q(q−1)/2`
* total:            `(q−1)+(q−1)+(q−1)(q−2)/2+q(q−1)/2 = q²−1`.

Carrying these out rigorously requires the constant class-size lemmas
(centralizer orders `q²−1`, `q²+q`, `q²−q` for the three non-central types),
which are a separate, substantial piece of infrastructure.
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2' := Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

namespace GL2

section Invariance

variable {p n}

/-- A scalar matrix is central: it commutes with every group element. -/
lemma val_mul_comm_of_isScalar {g : GL2' p n} (hg : GL2.IsScalar g)
    (c : GL2' p n) : (c * g).val = (g * c).val := by
  rw [GL2.isScalar_iff] at hg
  obtain ⟨h01, h10, h00⟩ := hg
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h00, mul_comm]

/-- Conjugating a scalar matrix returns the same matrix (scalars are central). -/
lemma val_conj_of_isScalar {g : GL2' p n} (hg : GL2.IsScalar g) (c : GL2' p n) :
    (c * g * c⁻¹).val = g.val := by
  have hcomm := val_mul_comm_of_isScalar hg c
  have hstep : (c * g * c⁻¹).val = (g * c * c⁻¹).val := by
    simp only [Units.val_mul] at hcomm ⊢; rw [hcomm]
  rw [hstep]
  simp only [mul_inv_cancel_right]

/-- `IsScalar` is a conjugation invariant: `x⁻¹ g x` is scalar iff `g` is. -/
lemma isScalar_conj_iff (g x : GL2' p n) :
    GL2.IsScalar (x⁻¹ * g * x) ↔ GL2.IsScalar g := by
  constructor
  · intro h
    -- If `x⁻¹gx` is scalar it is central, so `g = x (x⁻¹gx) x⁻¹ = x⁻¹gx`.
    have hval : g.val = (x⁻¹ * g * x).val := by
      have h2 := val_conj_of_isScalar h x
      have hrw : (x * (x⁻¹ * g * x) * x⁻¹) = g := by group
      rw [hrw] at h2; exact h2
    rw [GL2.isScalar_iff, hval, ← GL2.isScalar_iff]; exact h
  · intro h
    -- Conjugating a scalar gives back the same value, hence still scalar.
    have hval : (x⁻¹ * g * x).val = g.val := by
      have h2 := val_conj_of_isScalar h x⁻¹
      simpa using h2
    rw [GL2.isScalar_iff, hval, ← GL2.isScalar_iff]; exact h

/-- The discriminant is a conjugation invariant, phrased for `x⁻¹ g x`.
Restatement of `Etingof.disc_conj_eq` in the `GL2'` synonym. -/
lemma disc_conj_eq' (g x : GL2' p n) :
    GL2.disc (x⁻¹ * g * x) = GL2.disc g :=
  Etingof.disc_conj_eq p n g x

/-- `IsParabolic` is a conjugation invariant. -/
lemma isParabolic_conj_iff (g x : GL2' p n) :
    GL2.IsParabolic (x⁻¹ * g * x) ↔ GL2.IsParabolic g := by
  unfold GL2.IsParabolic
  rw [disc_conj_eq', isScalar_conj_iff]

/-- `IsSplitSemisimple` is a conjugation invariant. -/
lemma isSplitSemisimple_conj_iff (g x : GL2' p n) :
    GL2.IsSplitSemisimple (x⁻¹ * g * x) ↔ GL2.IsSplitSemisimple g := by
  unfold GL2.IsSplitSemisimple
  rw [disc_conj_eq']

/-- `IsElliptic` is a conjugation invariant. -/
lemma isElliptic_conj_iff (g x : GL2' p n) :
    GL2.IsElliptic (x⁻¹ * g * x) ↔ GL2.IsElliptic g := by
  unfold GL2.IsElliptic
  rw [disc_conj_eq']

end Invariance

section Counts

variable {p n}

/-- Number of **scalar** conjugacy classes: the image of the scalar elements
under the quotient map `ConjClasses.mk`. Uses `Set.ncard`, so no decidability
instances are needed to state the definition. -/
noncomputable def numScalarClasses : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | GL2.IsScalar g}).ncard

/-- Number of **parabolic** conjugacy classes. -/
noncomputable def numParabolicClasses : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | GL2.IsParabolic g}).ncard

/-- Number of **split-semisimple** (hyperbolic) conjugacy classes. -/
noncomputable def numSplitSemisimpleClasses : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | GL2.IsSplitSemisimple g}).ncard

/-- Number of **elliptic** conjugacy classes. -/
noncomputable def numEllipticClasses : ℕ :=
  (ConjClasses.mk '' {g : GL2' p n | GL2.IsElliptic g}).ncard

/-- Two scalar matrices are conjugate only if they are equal (scalars are
central, so each scalar conjugacy class is a singleton). -/
lemma eq_of_isConj_of_isScalar {g h : GL2' p n} (hg : GL2.IsScalar g)
    (hconj : IsConj g h) : g = h := by
  rw [isConj_iff] at hconj
  obtain ⟨c, hc⟩ := hconj
  -- `c * g * c⁻¹ = g` because `g` is central; but that conjugate is `h`.
  have : (c * g * c⁻¹).val = g.val := val_conj_of_isScalar hg c
  have hgh : g = c * g * c⁻¹ := Units.ext this.symm
  rw [hgh, hc]

variable [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)]

/-- **Scalar count.** There are `q − 1` scalar conjugacy classes, one for each
nonzero scalar `x` (matching `GL2.card_isScalar`). -/
theorem numScalarClasses_eq (hn : n ≠ 0) :
    numScalarClasses (p := p) (n := n) = Fintype.card (GaloisField p n) - 1 := by
  -- `ConjClasses.mk` is injective on the scalar elements (each scalar class is a
  -- singleton), so the number of scalar classes equals the number of scalar
  -- elements, which is `q − 1` by `GL2.card_isScalar`.
  have hinj : Set.InjOn ConjClasses.mk {g : GL2' p n | GL2.IsScalar g} := by
    intro g hg _ _ hgh
    simp only [Set.mem_setOf_eq] at hg
    exact eq_of_isConj_of_isScalar hg (ConjClasses.mk_eq_mk_iff_isConj.mp hgh)
  rw [numScalarClasses, Set.ncard_image_of_injOn hinj]
  -- Rewrite the scalar set as the coercion of the scalar filter, then count.
  have hset : {g : GL2' p n | GL2.IsScalar g}
      = ↑(Finset.univ.filter fun g : GL2' p n => GL2.IsScalar g) := by
    ext g; simp
  rw [hset, Set.ncard_coe_finset, GL2.card_isScalar (p := p) hn]

/-- **Parabolic count.** There are `q − 1` parabolic conjugacy classes, one for
each nonzero `x` (representative `[[x,1],[0,x]]`).

Book argument: a parabolic class has `q² − 1` elements (the centralizer of
`[[x,1],[0,x]]` is `{[[t,u],[0,t]] : t ≠ 0}`, of order `q(q−1)`, and
`|G|/|C| = q(q+1)(q−1)² / (q(q−1)) = q²−1`). Dividing the total number of
parabolic elements `(q−1)(q²−1)` (`GL2.card_isParabolic`) by the class size
`q²−1` gives `q − 1`. -/
theorem numParabolicClasses_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    numParabolicClasses (p := p) (n := n) = Fintype.card (GaloisField p n) - 1 := by
  sorry

/-- **Split-semisimple count.** There are `(q−1)(q−2)/2` split-semisimple
(hyperbolic) conjugacy classes, one for each unordered pair `{x, y}` of distinct
nonzero eigenvalues.

Book argument: a hyperbolic class has `q² + q = q(q+1)` elements (the
centralizer of `diag(x,y)` with `x ≠ y` is the diagonal torus, of order
`(q−1)²`). Dividing the number of split-semisimple elements
`(q−1)(q−2)q(q+1)/2` (`GL2.card_isSplitSemisimple`) by `q(q+1)` gives
`(q−1)(q−2)/2`. -/
theorem numSplitSemisimpleClasses_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    numSplitSemisimpleClasses (p := p) (n := n) =
      (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) - 2) / 2 := by
  sorry

/-- **Elliptic count.** There are `q(q−1)/2` elliptic conjugacy classes (the
representatives `[[x, εy],[y, x]]` with `y ≠ 0`, identified up to `y ↦ −y`).

Book argument: an elliptic class has `q² − q = q(q−1)` elements (the centralizer
of an elliptic element is `𝔽_{q²}^×`, of order `q²−1`; see
`Etingof.centralizer_nonscalar_elliptic`). Dividing the number of elliptic
elements `q²(q−1)²/2` (`GL2.card_isElliptic`) by `q(q−1)` gives `q(q−1)/2`. -/
theorem numEllipticClasses_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    numEllipticClasses (p := p) (n := n) =
      Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  sorry

/-- **Total count.** `GL₂(𝔽_q)` has `q² − 1` conjugacy classes altogether — the
sum of the four type counts `(q−1) + (q−1) + (q−1)(q−2)/2 + q(q−1)/2 = q²−1`.
This is the number of irreducible representations of `GL₂(𝔽_q)`. -/
theorem card_conjClasses_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    Nat.card (ConjClasses (GL2' p n)) =
      Fintype.card (GaloisField p n) ^ 2 - 1 := by
  sorry

end Counts

end GL2

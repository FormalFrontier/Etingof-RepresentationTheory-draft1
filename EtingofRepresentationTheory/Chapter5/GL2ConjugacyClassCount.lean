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
* The **partition** `GL2.card_conjClasses_eq_sum` is proved fully: the total
  `Nat.card (ConjClasses (GL₂))` equals the sum of the four type counts, because
  the type predicates transfer across conjugacy (`GL2.isScalar_of_isConj` etc.)
  and are exhaustive, so their `ConjClasses.mk`-images partition the class set.
* The **grand total** `GL2.card_conjClasses_eq = q² − 1` is then *derived* from
  the partition plus the four per-type counts and the arithmetic identity
  `(q−1) + (q−1) + (q−1)(q−2)/2 + q(q−1)/2 = q² − 1` (valid since `q = pⁿ` is
  odd, so both divisions are exact). It carries no `sorry` of its own; it only
  inherits the deferred per-type counts below.

## What is deferred (top-down `sorry`s, with the book's argument recorded)

The parabolic / split-semisimple / elliptic per-type counts are stated but their
proofs are deferred. Each follows the book by dividing the element count of a
type by the (constant) size of a class of that type:

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

/-- `IsScalar` transfers across conjugacy (it is a class function). -/
lemma isScalar_of_isConj {g h : GL2' p n} (hc : IsConj g h) (hg : GL2.IsScalar g) :
    GL2.IsScalar h := by
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  simpa using (isScalar_conj_iff g c⁻¹).mpr hg

/-- `IsParabolic` transfers across conjugacy. -/
lemma isParabolic_of_isConj {g h : GL2' p n} (hc : IsConj g h) (hg : GL2.IsParabolic g) :
    GL2.IsParabolic h := by
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  simpa using (isParabolic_conj_iff g c⁻¹).mpr hg

/-- `IsSplitSemisimple` transfers across conjugacy. -/
lemma isSplitSemisimple_of_isConj {g h : GL2' p n} (hc : IsConj g h)
    (hg : GL2.IsSplitSemisimple g) : GL2.IsSplitSemisimple h := by
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  simpa using (isSplitSemisimple_conj_iff g c⁻¹).mpr hg

/-- Two type-images under `ConjClasses.mk` are disjoint provided no conjugate pair
realises both predicates. This is the class-level version of the element-level
disjointness facts `GL2.isScalar_not_isParabolic` etc. -/
lemma disjoint_conjImage {P Q : GL2' p n → Prop}
    (hPQ : ∀ g h, IsConj g h → P g → Q h → False) :
    Disjoint (ConjClasses.mk '' {g : GL2' p n | P g})
      (ConjClasses.mk '' {g : GL2' p n | Q g}) := by
  rw [Set.disjoint_left]
  rintro c ⟨g, hg, rfl⟩ ⟨h, hh, hmk⟩
  exact hPQ g h ((ConjClasses.mk_eq_mk_iff_isConj.mp hmk).symm) hg hh

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

/-- **Partition of the class set.** The total number of conjugacy classes of
`GL₂(𝔽_q)` is the sum of the four type counts. Proved fully: the four type
predicates are conjugation-invariant (`isScalar_of_isConj` etc.) and exhaustive
(`GL2.conjugacyClass_exhaustive`), so pushing them through `ConjClasses.mk`
partitions `ConjClasses (GL₂)` into four disjoint pieces. -/
theorem card_conjClasses_eq_sum :
    Nat.card (ConjClasses (GL2' p n)) =
      numScalarClasses (p := p) (n := n) + numParabolicClasses (p := p) (n := n) +
        numSplitSemisimpleClasses (p := p) (n := n) + numEllipticClasses (p := p) (n := n) := by
  haveI : Finite (GL2' p n) := Finite.of_fintype _
  haveI : Finite (ConjClasses (GL2' p n)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  simp only [numScalarClasses, numParabolicClasses, numSplitSemisimpleClasses, numEllipticClasses]
  set CS := ConjClasses.mk '' {g : GL2' p n | GL2.IsScalar g} with hCS
  set CP := ConjClasses.mk '' {g : GL2' p n | GL2.IsParabolic g} with hCP
  set CSS := ConjClasses.mk '' {g : GL2' p n | GL2.IsSplitSemisimple g} with hCSS
  set CE := ConjClasses.mk '' {g : GL2' p n | GL2.IsElliptic g} with hCE
  -- The four type-images cover every conjugacy class.
  have hcover : (Set.univ : Set (ConjClasses (GL2' p n))) = CS ∪ CP ∪ CSS ∪ CE := by
    ext c
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rcases GL2.conjugacyClass_exhaustive g with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Set.mem_image_of_mem _ h)))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_image_of_mem _ h)))
    · exact Or.inl (Or.inr (Set.mem_image_of_mem _ h))
    · exact Or.inr (Set.mem_image_of_mem _ h)
  -- Pairwise disjointness of the four type-images, from element-level disjointness.
  have dSP : Disjoint CS CP := GL2.disjoint_conjImage
    (fun g h hc hg hh => hh.2 (GL2.isScalar_of_isConj hc hg))
  have dSSS : Disjoint CS CSS := GL2.disjoint_conjImage
    (fun g h hc hg hh => GL2.isScalar_not_isSplitSemisimple h (GL2.isScalar_of_isConj hc hg) hh)
  have dSE : Disjoint CS CE := GL2.disjoint_conjImage
    (fun g h hc hg hh => GL2.isScalar_not_isElliptic h (GL2.isScalar_of_isConj hc hg) hh)
  have dPSS : Disjoint CP CSS := GL2.disjoint_conjImage
    (fun g h hc hg hh =>
      GL2.isParabolic_not_isSplitSemisimple h (GL2.isParabolic_of_isConj hc hg) hh)
  have dPE : Disjoint CP CE := GL2.disjoint_conjImage
    (fun g h hc hg hh => GL2.isParabolic_not_isElliptic h (GL2.isParabolic_of_isConj hc hg) hh)
  have dSSE : Disjoint CSS CE := GL2.disjoint_conjImage
    (fun g h hc hg hh =>
      GL2.isSplitSemisimple_not_isElliptic h (GL2.isSplitSemisimple_of_isConj hc hg) hh)
  have hSPuSS : Disjoint (CS ∪ CP) CSS := disjoint_sup_left.mpr ⟨dSSS, dPSS⟩
  have hSPSSuE : Disjoint (CS ∪ CP ∪ CSS) CE :=
    disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨dSE, dPE⟩, dSSE⟩
  rw [← Set.ncard_univ, hcover, Set.ncard_union_eq hSPSSuE, Set.ncard_union_eq hSPuSS,
    Set.ncard_union_eq dSP]

/-- **Total count.** `GL₂(𝔽_q)` has `q² − 1` conjugacy classes altogether — the
sum of the four type counts `(q−1) + (q−1) + (q−1)(q−2)/2 + q(q−1)/2 = q²−1`.
This is the number of irreducible representations of `GL₂(𝔽_q)`. Derived from the
fully-proved partition `card_conjClasses_eq_sum` and the four per-type counts. -/
theorem card_conjClasses_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    Nat.card (ConjClasses (GL2' p n)) =
      Fintype.card (GaloisField p n) ^ 2 - 1 := by
  rw [card_conjClasses_eq_sum, numScalarClasses_eq hn, numParabolicClasses_eq hp2 hn,
    numSplitSemisimpleClasses_eq hp2 hn, numEllipticClasses_eq hp2 hn]
  set q := Fintype.card (GaloisField p n) with hq
  -- `q = pⁿ` is odd and at least 3, so the two `/2` divisions are exact.
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hqval : q = p ^ n := by
    rw [hq, ← Nat.card_eq_fintype_card]; exact GaloisField.card p n hn
  have hqodd : Odd q := by
    rw [hqval]; exact (Nat.Prime.odd_of_ne_two hp.out hp2).pow
  have hq3 : 3 ≤ q := by
    rw [hqval]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨m, hm⟩ := hqodd
  have hm1 : 1 ≤ m := by omega
  have hq1 : q - 1 = 2 * m := by omega
  have hq2 : q - 2 = 2 * m - 1 := by omega
  have hdiv1 : (q - 1) * (q - 2) / 2 = m * (q - 2) := by
    rw [hq1, show 2 * m * (q - 2) = 2 * (m * (q - 2)) from by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hdiv2 : q * (q - 1) / 2 = q * m := by
    rw [hq1, show q * (2 * m) = 2 * (q * m) from by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hkey : m * (q - 2) + q * m = 4 * m ^ 2 := by
    rw [hq2, hm]
    have h4 : (2 * m - 1) + (2 * m + 1) = 4 * m := by omega
    calc m * (2 * m - 1) + (2 * m + 1) * m
        = m * ((2 * m - 1) + (2 * m + 1)) := by ring
      _ = m * (4 * m) := by rw [h4]
      _ = 4 * m ^ 2 := by ring
  have hRHS : q ^ 2 - 1 = 4 * m ^ 2 + 4 * m := by
    have : q ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by rw [hm]; ring
    omega
  rw [hdiv1, hdiv2, hq1]
  omega

end Counts

end GL2

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

/-! ## A class-count bridge

The three deferred per-type counts all follow the same recipe: divide the number
of *elements* of a type by the (constant) *size* of a conjugacy class of that
type. The size of the class of `g` is `|G| / |C_G(g)|` by orbit–stabilizer, so if
the centralizer order is constant equal to `d` across a conjugation-closed set
`S`, then every class contained in `S` has `|G| / d` elements and

  `(number of classes in S) · (|G| / d) = |S|`.

The lemma `ncard_conjClasses_image_mul_centralizerCard` below packages exactly
this, for an arbitrary finite group. Each per-type count then supplies the
type's element set `S`, its conjugation-closedness, and the constant centralizer
order `d`, and reads off the class count. -/

section ConjClassCount

open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

/-- **Orbit–stabilizer for conjugacy.** The fiber of `ConjClasses.mk` over a class
`c` (i.e. the conjugacy class itself) has cardinality `|G| / |C_G(g_c)|`, phrased
multiplicatively: `|fiber c| · |C_G(g_c)| = |G|`, where `g_c = c.out`. -/
private lemma fiber_card_mul_centralizerCard (c : ConjClasses G) :
    (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)).card
      * Nat.card (Subgroup.centralizer ({Quotient.out c} : Set G)) = Fintype.card G := by
  classical
  have hcarrier :
      (Finset.univ.filter (fun a : G => ConjClasses.mk a = c)) = c.carrier.toFinset := by
    ext a; simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hmk : ConjClasses.mk (Quotient.out c) = c := by
    rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq c
  have horb : MulAction.orbit (ConjAct G) (Quotient.out c) = c.carrier := by
    rw [ConjAct.orbit_eq_carrier_conjClasses, hmk]
  have hstab : Nat.card (Subgroup.centralizer ({Quotient.out c} : Set G))
      = Fintype.card (MulAction.stabilizer (ConjAct G) (Quotient.out c)) := by
    rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  rw [hcarrier, Set.toFinset_card, Fintype.card_congr (Equiv.setCongr horb.symm), hstab,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (Quotient.out c),
    ConjAct.card]

/-- **Class-count bridge.** Let `S` be a conjugation-closed subset of a finite group
`G` on which the centralizer order is constant equal to `d`. Then the number of
conjugacy classes meeting `S`, namely `(ConjClasses.mk '' S).ncard`, times the
common class size `|G| / d`, equals `|S|`.

Each class contained in `S` has `|G| / d` elements by orbit–stabilizer
(`fiber_card_mul_centralizerCard`); summing over the classes gives `|S|`. -/
theorem ncard_conjClasses_image_mul_centralizerCard {S : Set G}
    (hclosed : ∀ g ∈ S, ∀ x : G, x * g * x⁻¹ ∈ S)
    {d : ℕ} (hd : ∀ g ∈ S, Nat.card (Subgroup.centralizer ({g} : Set G)) = d) :
    (ConjClasses.mk '' S).ncard * (Fintype.card G / d) = S.ncard := by
  classical
  haveI : Fintype S := Fintype.ofFinite _
  -- Membership transfers along conjugacy: a conjugate of an element of `S` is in `S`.
  have hmem : ∀ {a b : G}, b ∈ S → IsConj a b → a ∈ S := by
    intro a b hb hconj
    rw [isConj_iff] at hconj
    obtain ⟨x, hx⟩ := hconj
    have hmemx : x⁻¹ * b * (x⁻¹)⁻¹ ∈ S := hclosed b hb x⁻¹
    have hax : a = x⁻¹ * b * (x⁻¹)⁻¹ := by rw [← hx]; group
    rw [hax]; exact hmemx
  set t : Finset (ConjClasses G) := S.toFinset.image ConjClasses.mk with ht
  have himg : ConjClasses.mk '' S = (↑t : Set (ConjClasses G)) := by
    rw [ht, Finset.coe_image, Set.coe_toFinset]
  -- Every fiber over a class in `t` has exactly `|G| / d` elements.
  have hfiber : ∀ c ∈ t, (S.toFinset.filter (fun a => ConjClasses.mk a = c)).card
      = Fintype.card G / d := by
    intro c hc
    rw [ht, Finset.mem_image] at hc
    obtain ⟨b, hbf, hbc⟩ := hc
    rw [Set.mem_toFinset] at hbf
    -- The fiber inside `S` is the whole fiber, since `S` is conjugation-closed.
    have hfe : S.toFinset.filter (fun a => ConjClasses.mk a = c)
        = Finset.univ.filter (fun a => ConjClasses.mk a = c) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, Set.mem_toFinset, true_and]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      have hconj : IsConj a b := ConjClasses.mk_eq_mk_iff_isConj.mp (h.trans hbc.symm)
      exact hmem hbf hconj
    have hout : Quotient.out c ∈ S := by
      have hmkc : ConjClasses.mk (Quotient.out c) = c := by
        rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq c
      have hconj : IsConj (Quotient.out c) b :=
        ConjClasses.mk_eq_mk_iff_isConj.mp (hmkc.trans hbc.symm)
      exact hmem hbf hconj
    have hkey := fiber_card_mul_centralizerCard c
    rw [hd _ hout] at hkey
    have hdpos : 0 < d := by
      have hpos : 0 < Nat.card (Subgroup.centralizer ({Quotient.out c} : Set G)) := Nat.card_pos
      rw [hd _ hout] at hpos; exact hpos
    rw [hfe, ← hkey, Nat.mul_div_cancel _ hdpos]
  -- Sum the fiber cardinalities over the classes.
  have hH : ∀ a ∈ S.toFinset, ConjClasses.mk a ∈ t := by
    intro a ha; rw [ht]; exact Finset.mem_image_of_mem _ ha
  have hsum : S.toFinset.card = t.card * (Fintype.card G / d) := by
    rw [Finset.card_eq_sum_card_fiberwise hH, Finset.sum_congr rfl hfiber,
      Finset.sum_const, smul_eq_mul]
  rw [himg, Set.ncard_coe_finset, Set.ncard_eq_toFinset_card', hsum]

end ConjClassCount

/-! ## Commutant of a non-scalar 2×2 matrix

For a non-scalar `A : Matrix (Fin 2) (Fin 2) F`, the commutant
`{M : M * A = A * M}` is exactly `{α • 1 + β • A}`, a 2-dimensional space (`A` and `1`
are linearly independent, and any commuting matrix is a combination of them). Over a
finite field of `q` elements this space has `q²` elements, and the invertible ones — the
centralizer of `A` in `GLₙ` — are exactly the `(α, β)` with `det (α • 1 + β • A) ≠ 0`.
The determinant is the quadratic form `α² + tr(A)·αβ + det(A)·β²`, whose number of zeros
is governed by the discriminant `tr² − 4·det = disc(A)`, giving the three per-type
centralizer orders. -/

section MatrixCommutant

variable {F : Type*} [Field F]

/-- Every matrix commuting with a non-scalar 2×2 matrix `A` is a linear combination
`α • 1 + β • A`. -/
private lemma exists_smul_add_smul_of_commute {A M : Matrix (Fin 2) (Fin 2) F}
    (hns : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1))
    (hcomm : M * A = A * M) :
    ∃ α β : F, M = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A := by
  -- Entrywise commutation equations.
  have E00 := congrFun (congrFun hcomm 0) 0
  have E01 := congrFun (congrFun hcomm 0) 1
  have E10 := congrFun (congrFun hcomm 1) 0
  have E11 := congrFun (congrFun hcomm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at E00 E01 E10 E11
  -- Given a chosen `α β`, reduce `M = α•1+β•A` to the four entry equations.
  have fin4 : ∀ α β : F,
      M 0 0 = α + β * A 0 0 → M 0 1 = β * A 0 1 →
      M 1 0 = β * A 1 0 → M 1 1 = α + β * A 1 1 →
      M = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A := by
    intro α β h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.one_apply] using h00
    · simpa [Matrix.one_apply] using h01
    · simpa [Matrix.one_apply] using h10
    · simpa [Matrix.one_apply] using h11
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · -- Diagonal non-scalar case: `A 0 0 ≠ A 1 1`.
      have had : A 0 0 ≠ A 1 1 := fun h => hns ⟨hb, hc, h⟩
      have hne : A 0 0 - A 1 1 ≠ 0 := sub_ne_zero.mpr had
      set β := (M 0 0 - M 1 1) / (A 0 0 - A 1 1) with hβ
      refine ⟨M 1 1 - β * A 1 1, β, fin4 _ _ ?_ ?_ ?_ ?_⟩
      · rw [hβ]; field_simp; ring
      · -- M 0 1 = β * A 0 1 = 0
        rw [hb, mul_zero]
        have hz : M 0 1 * (A 1 1 - A 0 0) = 0 := by rw [hb] at E01; linear_combination E01
        exact (mul_eq_zero.mp hz).resolve_right (fun h => (Ne.symm had) (sub_eq_zero.mp h))
      · rw [hc, mul_zero]
        have hz : M 1 0 * (A 0 0 - A 1 1) = 0 := by rw [hc] at E10; linear_combination E10
        exact (mul_eq_zero.mp hz).resolve_right (fun h => hne h)
      · ring
    · -- `A 0 1 = 0`, `A 1 0 ≠ 0`.
      set β := M 1 0 / A 1 0 with hβ
      refine ⟨M 1 1 - β * A 1 1, β, fin4 _ _ ?_ ?_ ?_ ?_⟩
      · -- M 0 0 = α + β * A 0 0
        rw [hβ]
        have hM00 : M 0 0 - M 1 1 = M 1 0 / A 1 0 * (A 0 0 - A 1 1) := by
          rw [div_mul_eq_mul_div, eq_div_iff hc]; linear_combination -E10
        linear_combination hM00
      · -- M 0 1 = β * A 0 1 = 0
        rw [hb, mul_zero]
        have hz : M 0 1 * A 1 0 = 0 := by rw [hb] at E00; linear_combination E00
        exact (mul_eq_zero.mp hz).resolve_right hc
      · rw [hβ]; field_simp
      · ring
  · -- `A 0 1 ≠ 0`.
    set β := M 0 1 / A 0 1 with hβ
    refine ⟨M 1 1 - β * A 1 1, β, fin4 _ _ ?_ ?_ ?_ ?_⟩
    · -- M 0 0 = α + β * A 0 0
      rw [hβ]
      have hM00 : M 0 0 - M 1 1 = M 0 1 / A 0 1 * (A 0 0 - A 1 1) := by
        rw [div_mul_eq_mul_div, eq_div_iff hb]; linear_combination E01
      linear_combination hM00
    · rw [hβ]; field_simp
    · -- M 1 0 = β * A 1 0
      rw [hβ]
      have hM10 : M 1 0 * A 0 1 = M 0 1 * A 1 0 := by linear_combination E11
      rw [div_mul_eq_mul_div, eq_div_iff hb]; linear_combination hM10
    · ring

/-- For a non-scalar 2×2 matrix `A`, the map `(α, β) ↦ α • 1 + β • A` is injective:
`1` and `A` are linearly independent. -/
private lemma smul_one_add_smul_injective {A : Matrix (Fin 2) (Fin 2) F}
    (hns : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1)) :
    Function.Injective
      (fun ab : F × F => ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) + ab.2 • A) := by
  rintro ⟨α, β⟩ ⟨α', β'⟩ h
  simp only at h
  have e00 : α + β * A 0 0 = α' + β' * A 0 0 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 0) 0
  have e01 : β * A 0 1 = β' * A 0 1 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 0) 1
  have e10 : β * A 1 0 = β' * A 1 0 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 1) 0
  have e11 : α + β * A 1 1 = α' + β' * A 1 1 := by
    simpa [Matrix.one_apply] using congrFun (congrFun h 1) 1
  have hβ : β = β' := by
    by_contra hne
    have hd : β - β' ≠ 0 := sub_ne_zero.mpr hne
    have hA01 : A 0 1 = 0 := by
      have hz : (β - β') * A 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.mp hz).resolve_left hd
    have hA10 : A 1 0 = 0 := by
      have hz : (β - β') * A 1 0 = 0 := by linear_combination e10
      exact (mul_eq_zero.mp hz).resolve_left hd
    have hAd : A 0 0 = A 1 1 := by
      have hz : (β - β') * (A 0 0 - A 1 1) = 0 := by linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hd)
    exact hns ⟨hA01, hA10, hAd⟩
  have hα : α = α' := by rw [hβ] at e00; linear_combination e00
  exact Prod.ext hα hβ

/-- The determinant of `α • 1 + β • A` is the quadratic form
`α² + tr(A)·αβ + det(A)·β²`. -/
private lemma det_smul_one_add_smul (A : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A)
      = α ^ 2 + (A 0 0 + A 1 1) * (α * β)
        + (A 0 0 * A 1 1 - A 0 1 * A 1 0) * β ^ 2 := by
  have h00 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 0 0 = α + β * A 0 0 := by
    simp [Matrix.one_apply]
  have h01 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 0 1 = β * A 0 1 := by
    simp [Matrix.one_apply]
  have h10 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 1 0 = β * A 1 0 := by
    simp [Matrix.one_apply]
  have h11 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 1 1 = α + β * A 1 1 := by
    simp [Matrix.one_apply]
  rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring

variable [Fintype F] [DecidableEq F]

/-- Number of pairs `(α, β)` with `det (α • 1 + β • A) = 0`, given that for every
`β ≠ 0` the number of `α` making the determinant vanish is a constant `r`. The `β = 0`
row contributes the single pair `(0, 0)`, and each of the `q − 1` nonzero rows
contributes `r`. -/
private lemma card_detZero_pairs {A : Matrix (Fin 2) (Fin 2) F} {r : ℕ}
    (hr : ∀ β : F, β ≠ 0 →
      (Finset.univ.filter (fun α : F =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) = 0)).card = r) :
    (Finset.univ.filter (fun ab : F × F =>
        Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) + ab.2 • A) = 0)).card
      = 1 + (Fintype.card F - 1) * r := by
  -- Fiber over the second coordinate `β`.
  have key : (Finset.univ.filter (fun ab : F × F =>
        Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) F) + ab.2 • A) = 0)).card
      = ∑ β : F, (Finset.univ.filter (fun α : F =>
          Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) = 0)).card := by
    simp_rw [Finset.card_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [key, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F))]
  -- `β = 0` row: `det (α•1) = α² = 0` iff `α = 0`.
  have hf0 : (Finset.univ.filter (fun α : F =>
      Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + (0 : F) • A) = 0)).card = 1 := by
    have hrw : (Finset.univ.filter (fun α : F =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + (0 : F) • A) = 0))
        = {(0 : F)} := by
      ext α
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [det_smul_one_add_smul]
      constructor
      · intro h
        have hα : α ^ 2 = 0 := by linear_combination h
        exact pow_eq_zero_iff (by norm_num) |>.mp hα
      · intro h; rw [h]; ring
    rw [hrw, Finset.card_singleton]
  -- Nonzero rows: each contributes `r`.
  have hsum : ∑ β ∈ Finset.univ.erase (0 : F),
      (Finset.univ.filter (fun α : F =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) = 0)).card
      = (Fintype.card F - 1) * r := by
    rw [Finset.sum_congr rfl (fun β hβ => hr β (Finset.ne_of_mem_erase hβ))]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
  rw [hf0, hsum]

end MatrixCommutant

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

/-- For a **non-scalar** `g ∈ GL₂(𝔽_q)`, the centralizer order equals the number of
pairs `(α, β) ∈ 𝔽_q²` with `det (α • 1 + β • g) ≠ 0`. The centralizer of `g` in the
matrix ring is the 2-dimensional commutant algebra `{α • 1 + β • g}`
(`exists_smul_add_smul_of_commute`, `smul_one_add_smul_injective`), whose units are
exactly those combinations with nonzero determinant. -/
private lemma centralizerCard_eq_card_units {g : GL2' p n} (hns : ¬ GL2.IsScalar g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Finset.univ.filter (fun ab : GaloisField p n × GaloisField p n =>
          Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n))
            + ab.2 • g.val) ≠ 0)).card := by
  have hns' : ¬ (g.val 0 1 = 0 ∧ g.val 1 0 = 0 ∧ g.val 0 0 = g.val 1 1) :=
    fun h => hns ((GL2.isScalar_iff g).mpr h)
  -- `α•1+β•g` commutes with `g`.
  have hcomm_mat : ∀ α β : GaloisField p n,
      (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) * g.val
        = g.val * (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) := by
    intro α β
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  -- Value of `mkOfDetNeZero`.
  have hvalMk : ∀ (α β : GaloisField p n)
      (h : Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) ≠ 0),
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) h).val
        = α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val := by
    intro α β h
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
  -- The bijection between good pairs and the centralizer.
  let f : {ab : GaloisField p n × GaloisField p n //
      Matrix.det (ab.1 • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + ab.2 • g.val) ≠ 0}
      → ↥(Subgroup.centralizer ({g} : Set (GL2' p n))) := fun ab =>
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        (ab.1.1 • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + ab.1.2 • g.val) ab.2, by
      rw [Subgroup.mem_centralizer_iff]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hvalMk]
      exact (hcomm_mat ab.1.1 ab.1.2).symm⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨α, β⟩, hab⟩ ⟨⟨α', β'⟩, hab'⟩ heq
      have hvv : α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val
          = α' • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β' • g.val := by
        have h1 := congrArg
          (fun u : ↥(Subgroup.centralizer ({g} : Set (GL2' p n))) => (u : GL2' p n).val) heq
        simpa [f, hvalMk] using h1
      exact Subtype.ext (smul_one_add_smul_injective hns' (A := g.val) hvv)
    · rintro ⟨M, hM⟩
      rw [Subgroup.mem_centralizer_iff] at hM
      have hcomm : M.val * g.val = g.val * M.val := by
        have hgm := hM g (Set.mem_singleton g)
        have h2 := congrArg (fun u : GL2' p n => u.val) hgm
        rw [Units.val_mul, Units.val_mul] at h2
        exact h2.symm
      obtain ⟨α, β, hαβ⟩ := exists_smul_add_smul_of_commute hns' hcomm
      have hMdet : Matrix.det M.val ≠ 0 := by
        have hu := M.isUnit
        rw [Matrix.isUnit_iff_isUnit_det] at hu
        exact hu.ne_zero
      have hdet : Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n))
          + β • g.val) ≠ 0 := by rw [← hαβ]; exact hMdet
      refine ⟨⟨(α, β), hdet⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      show (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet).val = M.val
      rw [hvalMk]; exact hαβ.symm
  rw [(Nat.card_congr (Equiv.ofBijective f hbij)).symm, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

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

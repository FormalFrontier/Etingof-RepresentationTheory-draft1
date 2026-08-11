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
image.

## What is proved here

* The four type predicates (`GL2.IsScalar`, `GL2.IsParabolic`,
  `GL2.IsSplitSemisimple`, `GL2.IsElliptic`) are conjugation-invariant
  (`GL2.isScalar_conj_iff`, `GL2.isParabolic_conj_iff`, etc.). This is what
  makes "the type of a conjugacy class" well defined, and follows from
  `Etingof.disc_conj_eq` (discriminant is a class function) together with the
  centrality of scalar matrices.
* The **scalar count** `GL2.numScalarClasses = q − 1`: each
  scalar matrix is central, so its conjugacy class is a singleton and
  `ConjClasses.mk` is injective on the scalar set; the count therefore equals
  the number of scalar elements, which is `q − 1` by `GL2.card_isScalar`.
* The **partition** `GL2.card_conjClasses_eq_sum`: the total
  `Nat.card (ConjClasses (GL₂))` equals the sum of the four type counts, because
  the type predicates transfer across conjugacy (`GL2.isScalar_of_isConj` etc.)
  and are exhaustive, so their `ConjClasses.mk`-images partition the class set.
* The **grand total** `GL2.card_conjClasses_eq = q² − 1` follows from
  the partition plus the four per-type counts and the arithmetic identity
  `(q−1) + (q−1) + (q−1)(q−2)/2 + q(q−1)/2 = q² − 1` (valid since `q = pⁿ` is
  odd, so both divisions are exact).

## The three per-type counts

The parabolic / split-semisimple / elliptic per-type counts are proved by the
book's recipe: divide the element count of a type by the (constant) size of a
class of that type:

* parabolic:        `(q−1)(q²−1) / (q²−1)      = q−1`
* split semisimple: `(q−1)(q−2)q(q+1)/2 / (q²+q) = (q−1)(q−2)/2`
* elliptic:         `q²(q−1)²/2 / (q²−q)         = q(q−1)/2`
* total:            `(q−1)+(q−1)+(q−1)(q−2)/2+q(q−1)/2 = q²−1`.

The constant class-size lemmas come from the centralizer orders `q(q−1)`,
`(q−1)²`, `q²−1` (parabolic, split-semisimple, elliptic). These are computed
uniformly in `centralizerCard_parabolic`, `centralizerCard_splitSemisimple`,
`centralizerCard_elliptic`: for a non-scalar `g`, the centralizer in the matrix
ring is the 2-dimensional commutant algebra `{α • 1 + β • g}`
(`exists_smul_add_smul_of_commute`), and its units, the group centralizer, are
counted by the number of `(α, β)` with `det (α • 1 + β • g) ≠ 0`, which the
determinant quadratic `α² + tr·αβ + det·β²` (discriminant `disc g`) resolves into
the three type-dependent values via the quadratic root counts. The per-type
counts are then combined by `count_from_bridge`.
-/

/-! ## A class-count identity

The three per-type counts all follow the same recipe: divide the number
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

/-- **Class-count identity.** Let `S` be a conjugation-closed subset of a finite group
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
finite field of `q` elements this space has `q²` elements, and the invertible ones (the
centralizer of `A` in `GLₙ`) are exactly the `(α, β)` with `det (α • 1 + β • A) ≠ 0`.
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
    simp
  have h01 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 0 1 = β * A 0 1 := by
    simp
  have h10 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 1 0 = β * A 1 0 := by
    simp
  have h11 : (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A) 1 1 = α + β * A 1 1 := by
    simp
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
      change (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet).val = M.val
      rw [hvalMk]; exact hαβ.symm
  rw [(Nat.card_congr (Equiv.ofBijective f hbij)).symm, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **Centralizer order of a non-scalar element**, in terms of the per-`β` root count `r`
of the determinant quadratic: `|C_G(g)| = q² − (1 + (q−1)·r)`. Combines the
commutant-units description (`centralizerCard_eq_card_units`) with the fiberwise det-zero
count (`card_detZero_pairs`). -/
private lemma centralizerCard_of_nonscalar {g : GL2' p n} (hns : ¬ GL2.IsScalar g)
    {r : ℕ} (hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = r) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) ^ 2
        - (1 + (Fintype.card (GaloisField p n) - 1) * r) := by
  rw [centralizerCard_eq_card_units hns]
  have hz := card_detZero_pairs (A := g.val) hr
  simp only [ne_eq]
  rw [Finset.filter_not, Finset.card_univ_sdiff, Fintype.card_prod, hz, ← pow_two]

/-- The determinant discriminant `((tr)·β)² − 4·(det)·β² = β²·disc(g)`. -/
private lemma quadDisc_eq (g : GL2' p n) (β : GaloisField p n) :
    ((g.val 0 0 + g.val 1 1) * β) ^ 2
      - 4 * 1 * ((g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) * β ^ 2)
      = β ^ 2 * GL2.disc g := by
  rw [GL2.disc_eq]; ring

/-- Rewrite the `α`-fiber `{α : det (α•1+β•g) = 0}` as the quadratic filter
`{α : α² + (tr·β)·α + (det·β²) = 0}`. -/
private lemma alphaFiber_eq (g : GL2' p n) (β : GaloisField p n) :
    (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0))
      = (Finset.univ.filter (fun α : GaloisField p n =>
        (1 : GaloisField p n) * α ^ 2 + ((g.val 0 0 + g.val 1 1) * β) * α
          + (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) * β ^ 2 = 0)) := by
  apply Finset.filter_congr
  intro α _
  rw [det_smul_one_add_smul]
  constructor <;> intro h <;> linear_combination h

/-- Centralizer order of a **parabolic** element is `q(q−1)`. -/
private lemma centralizerCard_parabolic {g : GL2' p n} (hg : GL2.IsParabolic g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) := by
  obtain ⟨hdisc, hns⟩ := hg
  have hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = 1 := by
    intro β _
    rw [alphaFiber_eq]
    apply Etingof.quadratic_one_root_zero_disc _ _ _ one_ne_zero
    rw [quadDisc_eq, hdisc, mul_zero]
  rw [centralizerCard_of_nonscalar hns hr]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := GaloisField p n))
  rw [hm]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, mul_one]
  have e1 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  have e2 : (m + 1) * m = m ^ 2 + m := by ring
  omega

/-- In `GaloisField p n` with `p ≠ 2`, `2 ≠ 0`. -/
private lemma two_ne_zero_galoisField (hp2 : p ≠ 2) : (2 : GaloisField p n) ≠ 0 := by
  intro h
  have hchar2 : CharP (GaloisField p n) 2 :=
    (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
  have hp_char : CharP (GaloisField p n) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
  exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)

/-- Centralizer order of a **split-semisimple** element is `(q−1)²`. -/
private lemma centralizerCard_splitSemisimple (hp2 : p ≠ 2) {g : GL2' p n}
    (hg : GL2.IsSplitSemisimple g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Fintype.card (GaloisField p n) - 1) ^ 2 := by
  obtain ⟨hdne, hsq⟩ := hg
  have hns : ¬ GL2.IsScalar g := fun hsc => GL2.isScalar_not_isSplitSemisimple g hsc ⟨hdne, hsq⟩
  haveI : NeZero (2 : GaloisField p n) := ⟨two_ne_zero_galoisField hp2⟩
  have hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = 2 := by
    intro β hβ
    rw [alphaFiber_eq]
    refine Etingof.quadratic_two_roots _ _ _ one_ne_zero ?_ ?_
    · rw [quadDisc_eq]; exact mul_ne_zero (pow_ne_zero 2 hβ) hdne
    · rw [quadDisc_eq]; exact IsSquare.mul ⟨β, by ring⟩ hsq
  rw [centralizerCard_of_nonscalar hns hr]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := GaloisField p n))
  rw [hm]
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  have e1 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  omega

/-- Centralizer order of an **elliptic** element is `q² − 1`. -/
private lemma centralizerCard_elliptic {g : GL2' p n} (hg : GL2.IsElliptic g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  have hns : ¬ GL2.IsScalar g := fun hsc => GL2.isScalar_not_isElliptic g hsc hg
  have hr : ∀ β : GaloisField p n, β ≠ 0 →
      (Finset.univ.filter (fun α : GaloisField p n =>
        Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) + β • g.val) = 0)).card
        = 0 := by
    intro β hβ
    rw [alphaFiber_eq]
    refine Etingof.quadratic_no_roots _ _ _ one_ne_zero ?_
    rw [quadDisc_eq]
    rintro ⟨s, hs⟩
    exact hg ⟨s * β⁻¹, by field_simp; linear_combination hs⟩
  rw [centralizerCard_of_nonscalar hns hr]
  simp

omit [DecidableEq (GaloisField p n)] in
/-- `|GL₂(𝔽_q)| = (q²−1)(q²−q)`. -/
private lemma card_GL2_eq :
    Fintype.card (GL2' p n)
      = (Fintype.card (GaloisField p n) ^ 2 - 1)
        * (Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)) := by
  have h := Matrix.card_GL_field (𝔽 := GaloisField p n) 2
  rw [Nat.card_eq_fintype_card] at h
  rw [h]; simp [Fin.prod_univ_two, pow_zero, pow_one]

omit [DecidableEq (GaloisField p n)] in
omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] in
/-- The public, instance-free order formula `|GL₂(𝔽_q)| = (q²−1)(q²−q)`. -/
theorem card_generalLinearGroup_two :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
      = (Nat.card (GaloisField p n) ^ 2 - 1)
        * (Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)) := by
  letI := Fintype.ofFinite (GaloisField p n)
  simpa [Fin.prod_univ_two, pow_zero, pow_one] using
    (Matrix.card_GL_field (𝔽 := GaloisField p n) 2)

omit [Fintype (GaloisField p n)] [DecidableEq (GaloisField p n)] [Fintype (GL2' p n)] in
/-- The public, factored order formula `|GL₂(𝔽_q)| = q(q+1)(q−1)²`. -/
theorem card_generalLinearGroup_two_factored :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n))
      = Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) + 1)
        * (Nat.card (GaloisField p n) - 1) ^ 2 := by
  rw [card_generalLinearGroup_two]
  have hsq : Nat.card (GaloisField p n) ^ 2 - 1
      = (Nat.card (GaloisField p n) - 1) * (Nat.card (GaloisField p n) + 1) := by
    rw [Nat.sub_mul]
    have hmul : Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) + 1)
        = Nat.card (GaloisField p n) ^ 2 + Nat.card (GaloisField p n) := by ring
    rw [hmul, one_mul]
    omega
  have hlin : Nat.card (GaloisField p n) ^ 2 - Nat.card (GaloisField p n)
      = Nat.card (GaloisField p n) * (Nat.card (GaloisField p n) - 1) := by
    rw [Nat.mul_sub_left_distrib]
    simp only [mul_one, pow_two]
  rw [hsq, hlin]
  ring

/-- `q = pⁿ ≥ 3` when `p ≠ 2`. -/
private lemma card_ge_three (hp2 : p ≠ 2) (hn : n ≠ 0) :
    3 ≤ Fintype.card (GaloisField p n) := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hn)

/-- **Per-type count.** Given a conjugation-closed type `P` with constant
centralizer order `d`, if the type has `cardS` elements, each class has `classSize`
elements (`= |G|/d > 0`), and `target · classSize = cardS`, then there are exactly
`target` classes of type `P`. -/
private lemma count_from_bridge {P : GL2' p n → Prop}
    (hclosed : ∀ g ∈ {g : GL2' p n | P g}, ∀ x : GL2' p n,
      x * g * x⁻¹ ∈ {g : GL2' p n | P g})
    {d : ℕ}
    (hd : ∀ g ∈ {g : GL2' p n | P g},
      Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n))) = d)
    {cardS target classSize : ℕ}
    (hSncard : {g : GL2' p n | P g}.ncard = cardS)
    (hclass : Fintype.card (GL2' p n) / d = classSize)
    (hpos : 0 < classSize)
    (harith : target * classSize = cardS) :
    (ConjClasses.mk '' {g : GL2' p n | P g}).ncard = target := by
  have hbridge := ncard_conjClasses_image_mul_centralizerCard hclosed hd
  rw [hSncard, hclass] at hbridge
  exact Nat.eq_of_mul_eq_mul_right hpos (hbridge.trans harith.symm)

/-- For `2 ∣ a`, `(a / 2) * b = (a * b) / 2`. -/
private lemma half_mul (a b : ℕ) (h : 2 ∣ a) : a / 2 * b = a * b / 2 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2),
    show 2 * k * b = 2 * (k * b) by ring, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

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
  rw [numScalarClasses, Set.InjOn.ncard_image hinj]
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
  simp only [numParabolicClasses]
  have hq3 := card_ge_three (p := p) (n := n) hp2 hn
  have hqe : Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) := by
    obtain ⟨m, hm⟩ :=
      Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
    rw [hm]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have : (m + 1) ^ 2 = (m + 1) * m + (m + 1) := by ring
    omega
  apply count_from_bridge (P := fun g => GL2.IsParabolic g)
    (cardS := (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) ^ 2 - 1))
    (target := Fintype.card (GaloisField p n) - 1)
    (classSize := Fintype.card (GaloisField p n) ^ 2 - 1)
  case hclosed =>
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact GL2.isParabolic_of_isConj (isConj_iff.mpr ⟨x, rfl⟩) hg
  case hd =>
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    exact centralizerCard_parabolic hg
  case hSncard =>
    rw [show {g : GL2' p n | GL2.IsParabolic g}
        = ↑(Finset.univ.filter (fun g : GL2' p n => GL2.IsParabolic g)) from by ext g; simp,
      Set.ncard_coe_finset, GL2.card_isParabolic hp2 hn]
  case hclass =>
    rw [card_GL2_eq, hqe]
    exact Nat.mul_div_cancel _ (Nat.mul_pos (by omega) (by omega))
  case hpos =>
    have : 1 < Fintype.card (GaloisField p n) ^ 2 := by nlinarith [hq3]
    omega
  case harith => ring

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
  simp only [numSplitSemisimpleClasses]
  have hq3 := card_ge_three (p := p) (n := n) hp2 hn
  have hqodd : Odd (Fintype.card (GaloisField p n)) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
    exact (Nat.Prime.odd_of_ne_two hp.out hp2).pow
  obtain ⟨m, hm⟩ := hqodd
  have hq1 : Fintype.card (GaloisField p n) - 1 = 2 * m := by omega
  have hGLfact : Fintype.card (GL2' p n)
      = (Fintype.card (GaloisField p n) - 1) ^ 2
        * (Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) + 1)) := by
    rw [card_GL2_eq]
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
    rw [hk]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have h1 : (k + 1) ^ 2 - 1 = k ^ 2 + 2 * k := by
      have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      omega
    have h2 : (k + 1) ^ 2 - (k + 1) = (k + 1) * k := by
      have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
      omega
    rw [h1, h2]; ring
  apply count_from_bridge (P := fun g => GL2.IsSplitSemisimple g)
    (cardS := (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) - 2)
      * Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) + 1) / 2)
    (target := (Fintype.card (GaloisField p n) - 1) * (Fintype.card (GaloisField p n) - 2) / 2)
    (classSize := Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) + 1))
  case hclosed =>
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact GL2.isSplitSemisimple_of_isConj (isConj_iff.mpr ⟨x, rfl⟩) hg
  case hd =>
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    exact centralizerCard_splitSemisimple hp2 hg
  case hSncard =>
    rw [show {g : GL2' p n | GL2.IsSplitSemisimple g}
        = ↑(Finset.univ.filter (fun g : GL2' p n => GL2.IsSplitSemisimple g)) from by ext g; simp,
      Set.ncard_coe_finset, GL2.card_isSplitSemisimple hp2 hn]
  case hclass =>
    rw [hGLfact]
    exact Nat.mul_div_cancel_left _ (pow_pos (by omega) 2)
  case hpos => exact Nat.mul_pos (by omega) (by omega)
  case harith =>
    rw [half_mul _ _
      ⟨m * (Fintype.card (GaloisField p n) - 2), by rw [hq1]; ring⟩]
    congr 1; ring

/-- **Elliptic count.** There are `q(q−1)/2` elliptic conjugacy classes (the
representatives `[[x, εy],[y, x]]` with `y ≠ 0`, identified up to `y ↦ −y`).

Book argument: an elliptic class has `q² − q = q(q−1)` elements (the centralizer
of an elliptic element is `𝔽_{q²}^×`, of order `q²−1`; see
`Etingof.centralizer_nonscalar_elliptic`). Dividing the number of elliptic
elements `q²(q−1)²/2` (`GL2.card_isElliptic`) by `q(q−1)` gives `q(q−1)/2`. -/
theorem numEllipticClasses_eq (hp2 : p ≠ 2) (hn : n ≠ 0) :
    numEllipticClasses (p := p) (n := n) =
      Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2 := by
  simp only [numEllipticClasses]
  have hq3 := card_ge_three (p := p) (n := n) hp2 hn
  have hqodd : Odd (Fintype.card (GaloisField p n)) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
    exact (Nat.Prime.odd_of_ne_two hp.out hp2).pow
  obtain ⟨m, hm⟩ := hqodd
  have hq1 : Fintype.card (GaloisField p n) - 1 = 2 * m := by omega
  have hq9 : 9 ≤ Fintype.card (GaloisField p n) ^ 2 := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hq3 2
  apply count_from_bridge (P := fun g => GL2.IsElliptic g)
    (cardS := Fintype.card (GaloisField p n) ^ 2 * (Fintype.card (GaloisField p n) - 1) ^ 2 / 2)
    (target := Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) / 2)
    (classSize := Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1))
  case hclosed =>
    intro g hg x
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h := (GL2.isElliptic_conj_iff g x⁻¹).mpr hg
    rwa [inv_inv] at h
  case hd =>
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    exact centralizerCard_elliptic hg
  case hSncard =>
    rw [show {g : GL2' p n | GL2.IsElliptic g}
        = ↑(Finset.univ.filter (fun g : GL2' p n => GL2.IsElliptic g)) from by ext g; simp,
      Set.ncard_coe_finset, GL2.card_isElliptic hp2 hn]
  case hclass =>
    rw [card_GL2_eq,
      Nat.mul_div_cancel_left _
        (by omega : 0 < Fintype.card (GaloisField p n) ^ 2 - 1)]
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
    rw [hk]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
    omega
  case hpos => exact Nat.mul_pos (by omega) (by omega)
  case harith =>
    rw [half_mul _ _ ⟨Fintype.card (GaloisField p n) * m, by rw [hq1]; ring⟩]
    congr 1; ring

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

/-- **Total count.** `GL₂(𝔽_q)` has `q² − 1` conjugacy classes altogether: the
sum of the four type counts `(q−1) + (q−1) + (q−1)(q−2)/2 + q(q−1)/2 = q²−1`.
This is the number of irreducible representations of `GL₂(𝔽_q)`. It follows from the
partition `card_conjClasses_eq_sum` and the four per-type counts. -/
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

/-! ## Per-type centralizer orders and conjugacy-class sizes (Discussion 5.25.1)

Etingof's table in §5.25 lists, for each of the four conjugacy types, both the
order of the centralizer of a representative and the number of elements in an
individual conjugacy class:

| Type              | centralizer order   | class size (# elements) |
|-------------------|---------------------|-------------------------|
| scalar            | `(q²−1)(q²−q) = |G|`| `1`                     |
| parabolic         | `q(q−1)`            | `q² − 1`                |
| split semisimple  | `(q−1)²`            | `q² + q`                |
| elliptic          | `q² − 1`            | `q² − q`                |

The centralizer orders are the public forms of the proof-internal
`centralizerCard_parabolic`, `centralizerCard_splitSemisimple`,
`centralizerCard_elliptic` used above to count classes; here we expose them
(`GL2.centralizerCard_isScalar`, `GL2.centralizerCard_isParabolic`,
`GL2.centralizerCard_isSplitSemisimple`, `GL2.centralizerCard_isElliptic`) and read
off the per-element class sizes by orbit–stabilizer.

For `g : GL₂(𝔽_q)`, the conjugacy class of `g` is exactly the orbit of `g` under
the conjugation action `ConjAct (GL₂(𝔽_q))`
(`ConjAct.orbit_eq_carrier_conjClasses`), and orbit–stabilizer
(`GL2.orbit_card_mul_centralizerCard`) gives `|class of g| · |C_G(g)| = |G|`. -/

/-- **Orbit–stabilizer for conjugacy classes.** For any `g`, the size of the
conjugacy class of `g` (the orbit of `g` under `ConjAct`) times the centralizer
order equals `|G|`. -/
theorem orbit_card_mul_centralizerCard (g : GL2' p n) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
        * Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GL2' p n) := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct (GL2' p n)) g),
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (ConjAct.toConjAct (G := GL2' p n)).toEquiv]
  exact (MulAction.stabilizer (ConjAct (GL2' p n)) g).index_mul_card

/-- **Centralizer order of a scalar element** is `|G| = (q²−1)(q²−q)`: a scalar
matrix is central, so its centralizer is the whole group. -/
theorem centralizerCard_isScalar {g : GL2' p n} (hg : GL2.IsScalar g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Fintype.card (GaloisField p n) ^ 2 - 1)
        * (Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n)) := by
  have htop : Subgroup.centralizer ({g} : Set (GL2' p n)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact Units.ext (val_mul_comm_of_isScalar hg x).symm
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, card_GL2_eq]

/-- **Centralizer order of a parabolic element** is `q(q−1)` (public form of
`centralizerCard_parabolic`). -/
theorem centralizerCard_isParabolic {g : GL2' p n} (hg : GL2.IsParabolic g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) :=
  centralizerCard_parabolic hg

/-- **Centralizer order of a split-semisimple element** is `(q−1)²` (public form of
`centralizerCard_splitSemisimple`); the centralizer is the diagonal torus. -/
theorem centralizerCard_isSplitSemisimple (hp2 : p ≠ 2) {g : GL2' p n}
    (hg : GL2.IsSplitSemisimple g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = (Fintype.card (GaloisField p n) - 1) ^ 2 :=
  centralizerCard_splitSemisimple hp2 hg

/-- **Centralizer order of an elliptic element** is `q² − 1` (public form of
`centralizerCard_elliptic`); the centralizer is the nonsplit torus `𝔽_{q²}^×`. -/
theorem centralizerCard_isElliptic {g : GL2' p n} (hg : GL2.IsElliptic g) :
    Nat.card (Subgroup.centralizer ({g} : Set (GL2' p n)))
      = Fintype.card (GaloisField p n) ^ 2 - 1 :=
  centralizerCard_elliptic hg

/-- `q = pⁿ ≥ 2` when `n ≠ 0`. -/
private lemma card_ge_two (hn : n ≠ 0) : 2 ≤ Fintype.card (GaloisField p n) := by
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn]
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right (by have := hp.out.two_le; omega)
      (Nat.one_le_iff_ne_zero.mpr hn)

/-- `q ^ 2 − q = q (q − 1)`. -/
private lemma sq_sub_self (q : ℕ) : q ^ 2 - q = q * (q - 1) := by
  cases q with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_sub_one]
    have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
    omega

/-- **Class size of a scalar element** is `1`: a scalar matrix is central, so its
conjugacy class is a singleton. -/
theorem classCard_isScalar {g : GL2' p n} (hg : GL2.IsScalar g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g) = 1 := by
  have hmul := orbit_card_mul_centralizerCard g
  rw [centralizerCard_isScalar hg, ← card_GL2_eq] at hmul
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos (by rw [one_mul]; exact hmul)

/-- **Class size of a parabolic element** is `q² − 1`. -/
theorem classCard_isParabolic (hn : n ≠ 0) {g : GL2' p n} (hg : GL2.IsParabolic g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
      = Fintype.card (GaloisField p n) ^ 2 - 1 := by
  have hq2 := card_ge_two (p := p) (n := n) hn
  have hmul := orbit_card_mul_centralizerCard g
  rw [centralizerCard_isParabolic hg, card_GL2_eq,
    sq_sub_self (Fintype.card (GaloisField p n))] at hmul
  have hpos : 0 < Fintype.card (GaloisField p n) * (Fintype.card (GaloisField p n) - 1) :=
    Nat.mul_pos (by omega) (by omega)
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- **Class size of a split-semisimple element** is `q² + q = q(q+1)`. -/
theorem classCard_isSplitSemisimple (hp2 : p ≠ 2) (hn : n ≠ 0) {g : GL2' p n}
    (hg : GL2.IsSplitSemisimple g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
      = Fintype.card (GaloisField p n) ^ 2 + Fintype.card (GaloisField p n) := by
  have hq2 := card_ge_two (p := p) (n := n) hn
  have hmul := orbit_card_mul_centralizerCard g
  rw [centralizerCard_isSplitSemisimple hp2 hg, card_GL2_eq] at hmul
  have hpos : 0 < (Fintype.card (GaloisField p n) - 1) ^ 2 := pow_pos (by omega) 2
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hmul]
  -- `(q²−1)(q²−q) = (q²+q)(q−1)²`
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_succ_of_ne_zero (show Fintype.card (GaloisField p n) ≠ 0 by omega)
  rw [hk]; simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  have h1 : (k + 1) ^ 2 - 1 = k ^ 2 + 2 * k := by
    have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    omega
  have h2 : (k + 1) ^ 2 - (k + 1) = (k + 1) * k := by
    have : (k + 1) ^ 2 = (k + 1) * k + (k + 1) := by ring
    omega
  rw [h1, h2]; ring

/-- **Class size of an elliptic element** is `q² − q = q(q−1)`. -/
theorem classCard_isElliptic (hn : n ≠ 0) {g : GL2' p n} (hg : GL2.IsElliptic g) :
    Nat.card (MulAction.orbit (ConjAct (GL2' p n)) g)
      = Fintype.card (GaloisField p n) ^ 2 - Fintype.card (GaloisField p n) := by
  have hq2 := card_ge_two (p := p) (n := n) hn
  have hmul := orbit_card_mul_centralizerCard g
  rw [centralizerCard_isElliptic hg, card_GL2_eq] at hmul
  have hq4 : 4 ≤ Fintype.card (GaloisField p n) ^ 2 := by nlinarith [hq2]
  have hpos : 0 < Fintype.card (GaloisField p n) ^ 2 - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hmul, mul_comm]

end Counts

/-! ## Representative / normal-form column (Discussion 5.25.1)

The last column of Etingof's §5.25 table displays a *canonical representative* for
each conjugacy type. Here we prove that every element of a given type is indeed
conjugate to the displayed representative:

| Type              | representative              | normalization              |
|-------------------|-----------------------------|----------------------------|
| scalar            | `x • I`                     | `x` its own value          |
| parabolic         | `!![x,1;0,x]`               | `x` the repeated eigenvalue|
| split semisimple  | `!![x,0;0,y]`, `x ≠ y`      | `{x,y}` unordered          |
| elliptic          | `!![x, ε·y;y, x]`, `y ≠ 0`  | `y ∼ −y`                   |

These are genuine `2 × 2` rational-canonical-form facts: for each type we exhibit an
explicit change-of-basis matrix `P ∈ GL₂` conjugating `g` to the representative.
The conjugations are verified at the level of the underlying matrices via
`GL2.isConj_of_val_conj`. -/

section Representatives

open scoped Matrix

variable {p n}

/-- **Conjugation helper.** If `g.val * P.val = P.val * r.val` for some `P : GL₂`, then
`g` and `r` are conjugate in `GL₂` (`r = P⁻¹ g P`). Used to certify each normal form
from an explicit change-of-basis matrix `P`. -/
lemma isConj_of_val_conj {g r : GL2' p n} (P : GL2' p n)
    (h : g.val * P.val = P.val * r.val) : IsConj g r := by
  refine isConj_iff.mpr ⟨P⁻¹, Units.ext ?_⟩
  have hPP : (P⁻¹ : GL2' p n).val * P.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, inv_inv]
  calc (P⁻¹ : GL2' p n).val * g.val * P.val
      = (P⁻¹ : GL2' p n).val * (g.val * P.val) := by rw [mul_assoc]
    _ = (P⁻¹ : GL2' p n).val * (P.val * r.val) := by rw [h]
    _ = (P⁻¹ : GL2' p n).val * P.val * r.val := by rw [mul_assoc]
    _ = r.val := by rw [hPP, one_mul]

/-- The determinant of a `GL₂` element is nonzero. -/
private lemma detval_ne_zero (g : GL2' p n) : Matrix.det g.val ≠ 0 := by
  intro h0
  have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [h0, zero_mul] at hdet1; exact one_ne_zero hdet1.symm

/-- The **scalar representative** `x • I` for a nonzero `x`. -/
noncomputable def scalarRepr (x : GaloisField p n) (hx : x ≠ 0) : GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (x • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)))
    (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
        exact pow_ne_zero 2 hx)

@[simp] lemma scalarRepr_val (x : GaloisField p n) (hx : x ≠ 0) :
    (scalarRepr x hx).val = x • (1 : Matrix (Fin 2) (Fin 2) (GaloisField p n)) := by
  simp [scalarRepr, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]

/-- **Scalar normal form.** Every scalar `g` equals `x • I` for a nonzero `x` (its own
diagonal value), hence is (trivially) conjugate to the scalar representative. -/
theorem exists_conj_isScalar {g : GL2' p n} (hg : GL2.IsScalar g) :
    ∃ (x : GaloisField p n) (hx : x ≠ 0), IsConj g (scalarRepr x hx) := by
  obtain ⟨h01, h10, h00⟩ := (GL2.isScalar_iff g).mp hg
  have hdet : Matrix.det g.val = g.val 0 0 * g.val 0 0 := by
    rw [Matrix.det_fin_two, h01, h10, ← h00]; ring
  have hx : g.val 0 0 ≠ 0 := by
    intro h0
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdet, h0, mul_zero, zero_mul] at hdet1
    exact one_ne_zero hdet1.symm
  refine ⟨g.val 0 0, hx, ?_⟩
  have heq : scalarRepr (g.val 0 0) hx = g := by
    apply Units.ext
    rw [scalarRepr_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h10, h00]
  rw [heq]

/-- The **parabolic (Jordan) representative** `!![x,1;0,x]` for a nonzero `x`. -/
noncomputable def jordanRepr (x : GaloisField p n) (hx : x ≠ 0) : GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, 1; 0, x]
    (by rw [Matrix.det_fin_two_of]; simpa using mul_ne_zero hx hx)

@[simp] lemma jordanRepr_val (x : GaloisField p n) (hx : x ≠ 0) :
    (jordanRepr x hx).val = !![x, 1; 0, x] := by
  simp [jordanRepr, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]

/-- Value of `mkOfDetNeZero` of an explicit matrix. -/
private lemma mkOfDetNeZero_val (M : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    (h : M.det ≠ 0) : (Matrix.GeneralLinearGroup.mkOfDetNeZero M h).val = M := by
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

/-- **Parabolic normal form.** Every parabolic `g` is conjugate to the Jordan block
`!![x,1;0,x]`, where `x` is the repeated eigenvalue `tr(g)/2`. -/
theorem exists_conj_isParabolic (hp2 : p ≠ 2) {g : GL2' p n} (hg : GL2.IsParabolic g) :
    ∃ (x : GaloisField p n) (hx : x ≠ 0), IsConj g (jordanRepr x hx) := by
  obtain ⟨hdisc, hns⟩ := hg
  rw [GL2.disc_eq] at hdisc
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
    have hp_char : CharP (GaloisField p n) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  -- The repeated eigenvalue `x = tr/2`.
  set x := (a + d) / 2 with hxdef
  have hx2 : a + d = 2 * x := by rw [hxdef]; field_simp
  -- `det g = x²`, hence `x ≠ 0`.
  have hkey : (a - x) ^ 2 + b * c = 0 := by
    have h4 : (4 : GaloisField p n) ≠ 0 := by
      have : (4 : GaloisField p n) = 2 * 2 := by ring
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    rw [mul_zero]
    linear_combination hdisc + (3 * a - d - 2 * x) * hx2
  have hdetx : Matrix.det g.val = x * x := by
    rw [Matrix.det_fin_two, ← ha, ← hb, ← hc', ← hd]
    linear_combination -hkey + a * hx2
  have hx : x ≠ 0 := by
    intro h0
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [hdetx, h0, mul_zero, zero_mul] at hdet1
    exact one_ne_zero hdet1.symm
  refine ⟨x, hx, ?_⟩
  by_cases hc0 : c = 0
  · -- `c = 0` forces `a = d = x`; representative conjugator `!![b,0;0,1]`.
    have hax : a = x := by
      have hk : (a - x) ^ 2 = 0 := by rw [← hkey, hc0, mul_zero, add_zero]
      have : a - x = 0 := by
        exact pow_eq_zero_iff (by norm_num) |>.mp hk
      linear_combination this
    have hdx : d = x := by linear_combination hx2 - hax
    have hbne : b ≠ 0 := by
      intro hb0
      exact hns ((GL2.isScalar_iff g).mpr ⟨hb0, hc0, by rw [← ha, ← hd, hax, hdx]⟩)
    have hPdet : Matrix.det (!![b, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField p n)) ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simpa using hbne
    refine isConj_of_val_conj (Matrix.GeneralLinearGroup.mkOfDetNeZero !![b, 0; 0, 1] hPdet) ?_
    rw [mkOfDetNeZero_val, jordanRepr_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd, hc0, hax, hdx] ;
      ring
  · -- `c ≠ 0`: representative conjugator `!![a-x,1;c,0]`, det `-c ≠ 0`.
    have hPdet : Matrix.det (!![a - x, 1; c, 0] : Matrix (Fin 2) (Fin 2) (GaloisField p n)) ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simpa using hc0
    refine isConj_of_val_conj (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a - x, 1; c, 0] hPdet) ?_
    rw [mkOfDetNeZero_val, jordanRepr_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
      first
        | linear_combination hkey
        | linear_combination c * hx2

/-- The **split-semisimple (diagonal) representative** `!![x,0;0,y]` for nonzero
`x, y`. -/
noncomputable def diagRepr (x y : GaloisField p n) (hx : x ≠ 0) (hy : y ≠ 0) : GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, 0; 0, y]
    (by rw [Matrix.det_fin_two_of]; simpa using mul_ne_zero hx hy)

@[simp] lemma diagRepr_val (x y : GaloisField p n) (hx : x ≠ 0) (hy : y ≠ 0) :
    (diagRepr x y hx hy).val = !![x, 0; 0, y] := by
  simp [diagRepr, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]

/-- **Split-semisimple normal form.** Every split-semisimple `g` is conjugate to a
diagonal matrix `!![x,0;0,y]` with distinct nonzero eigenvalues `x ≠ y` (the two
roots of the characteristic polynomial; the unordered pair `{x,y}` is the invariant). -/
theorem exists_conj_isSplitSemisimple (hp2 : p ≠ 2) {g : GL2' p n}
    (hg : GL2.IsSplitSemisimple g) :
    ∃ (x y : GaloisField p n) (hx : x ≠ 0) (hy : y ≠ 0),
      x ≠ y ∧ IsConj g (diagRepr x y hx hy) := by
  obtain ⟨hdne, hsq⟩ := hg
  rw [GL2.disc_eq] at hdne hsq
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  obtain ⟨s, hs⟩ := hsq
  -- `s` is a square root of the discriminant; nonzero since `disc ≠ 0`.
  have hsne : s ≠ 0 := by
    intro h0; apply hdne; rw [hs, h0, mul_zero]
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
    have hp_char : CharP (GaloisField p n) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)
  have h4 : (4 : GaloisField p n) ≠ 0 := by
    have : (4 : GaloisField p n) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  -- The two eigenvalues `x = (tr+s)/2`, `y = (tr-s)/2`.
  set x := (a + d + s) / 2 with hxdef
  set y := (a + d - s) / 2 with hydef
  have hx2 : 2 * x = a + d + s := by rw [hxdef]; field_simp
  have hy2 : 2 * y = a + d - s := by rw [hydef]; field_simp
  clear_value x y
  have hxysub : x - y = s := by
    have h2s : 2 * (x - y) = 2 * s := by linear_combination hx2 - hy2
    exact mul_left_cancel₀ h2 h2s
  -- Both eigenvalues satisfy the characteristic equation.
  have hxroot : x * x - (a + d) * x + (a * d - b * c) = 0 := by
    apply mul_left_cancel₀ h4; rw [mul_zero]
    linear_combination -hs + (2 * x - (a + d) + s) * hx2
  have hyroot : y * y - (a + d) * y + (a * d - b * c) = 0 := by
    apply mul_left_cancel₀ h4; rw [mul_zero]
    linear_combination -hs + (2 * y - (a + d) - s) * hy2
  -- `det g = x·y`, so both eigenvalues are nonzero.
  have hxy : x * y = a * d - b * c := by
    apply mul_left_cancel₀ h4
    linear_combination hs + (2 * y) * hx2 + (a + d + s) * hy2
  have hdetv : Matrix.det g.val = a * d - b * c := by
    rw [Matrix.det_fin_two, ← ha, ← hb, ← hc', ← hd]
  have hdet_ne : Matrix.det g.val ≠ 0 := by
    intro h0
    have hmul : g.val * (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdet1 : Matrix.det g.val * Matrix.det (g⁻¹ : GL2' p n).val = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [h0, zero_mul] at hdet1; exact one_ne_zero hdet1.symm
  have hxyne : x * y ≠ 0 := by rw [hxy, ← hdetv]; exact hdet_ne
  have hx0 : x ≠ 0 := fun h => hxyne (by rw [h, zero_mul])
  have hy0 : y ≠ 0 := fun h => hxyne (by rw [h, mul_zero])
  have hxney : x ≠ y := by
    intro h; apply hsne; rw [← hxysub, h, sub_self]
  by_cases hb0 : b = 0
  · by_cases hc0 : c = 0
    · -- Diagonal case `b = c = 0`: `g = diag(a,d)`; witnesses `a, d`.
      have hdetad : Matrix.det g.val = a * d := by rw [hdetv, hb0, zero_mul, sub_zero]
      have ha0 : a ≠ 0 := by
        intro h; apply hdet_ne; rw [hdetad, h, zero_mul]
      have hd0 : d ≠ 0 := by
        intro h; apply hdet_ne; rw [hdetad, h, mul_zero]
      have hane : a ≠ d := by
        intro h; apply hdne; rw [h, hb0]; ring
      refine ⟨a, d, ha0, hd0, hane, ?_⟩
      have heq : diagRepr a d ha0 hd0 = g := by
        apply Units.ext
        rw [diagRepr_val]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [← ha, ← hb, ← hc', ← hd, hb0, hc0]
      rw [heq]
    · -- `b = 0`, `c ≠ 0`: conjugator `!![x-d,y-d;c,c]`, det `c·s`.
      have hPdet : (!![x - d, y - d; c, c] :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        have : (x - d) * c - (y - d) * c = c * s := by rw [← hxysub]; ring
        rw [this]; exact mul_ne_zero hc0 hsne
      refine ⟨x, y, hx0, hy0, hxney, ?_⟩
      refine isConj_of_val_conj
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![x - d, y - d; c, c] hPdet) ?_
      rw [mkOfDetNeZero_val, diagRepr_val]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
        (try ring) <;> (try linear_combination -hxroot) ; (try linear_combination -hyroot)
  · -- `b ≠ 0`: conjugator `!![b,b;x-a,y-a]`, det `-b·s`.
    have hPdet : (!![b, b; x - a, y - a] :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      have : b * (y - a) - b * (x - a) = -(b * s) := by rw [← hxysub]; ring
      rw [this]; simpa using mul_ne_zero hb0 hsne
    refine ⟨x, y, hx0, hy0, hxney, ?_⟩
    refine isConj_of_val_conj
      (Matrix.GeneralLinearGroup.mkOfDetNeZero !![b, b; x - a, y - a] hPdet) ?_
    rw [mkOfDetNeZero_val, diagRepr_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
      (try ring) <;> (try linear_combination -hxroot) ; (try linear_combination -hyroot)

/-- **Companion form.** Every non-scalar `g ∈ GL₂` is conjugate to the companion matrix
`!![0,-det;1,tr]` of its characteristic polynomial. For a cyclic vector `v` (one with
`{v, g·v}` a basis), the change of basis `P = [v | g·v]` sends `g` to its companion
matrix: `g·(g·v) = tr·(g·v) - det·v` by Cayley–Hamilton, and the companion relation
`g·P = P·companion` then holds for **any** `v`; only invertibility of `P` (cyclicity of
`v`) is case-dependent. -/
private lemma isConj_companion {g : GL2' p n} (hns : ¬ GL2.IsScalar g)
    (t dt : GaloisField p n) (hdt : dt ≠ 0)
    (ht : t = g.val 0 0 + g.val 1 1) (hdtv : dt = Matrix.det g.val) :
    IsConj g (Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -dt; 1, t]
      (by rw [Matrix.det_fin_two_of]; simpa using hdt)) := by
  subst ht hdtv
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  -- The companion relation `g·P = P·companion` for `P = !![v0, a·v0+b·v1; v1, c·v0+d·v1]`.
  have key : ∀ v0 v1 : GaloisField p n,
      ∀ h : (!![v0, a * v0 + b * v1; v1, c * v0 + d * v1] :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)).det ≠ 0,
      IsConj g (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(0 : GaloisField p n), -Matrix.det g.val; 1, a + d]
        (by rw [Matrix.det_fin_two_of]; simpa using detval_ne_zero g)) := by
    intro v0 v1 h
    refine isConj_of_val_conj
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![v0, a * v0 + b * v1; v1, c * v0 + d * v1] h) ?_
    simp only [mkOfDetNeZero_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
        ← ha, ← hb, ← hc', ← hd] <;> ring
  by_cases hc0 : c = 0
  · by_cases hb0 : b = 0
    · -- Diagonal non-scalar (`a ≠ d`): cyclic vector `(1,1)`.
      have hane : a ≠ d := fun h => hns ((GL2.isScalar_iff g).mpr ⟨hb0, hc0, h⟩)
      refine key 1 1 ?_
      have hval : (!![(1 : GaloisField p n), a * 1 + b * 1; 1, c * 1 + d * 1]).det = d - a := by
        rw [Matrix.det_fin_two_of, hb0, hc0]; ring
      rw [hval]; exact sub_ne_zero.mpr (Ne.symm hane)
    · -- `c = 0`, `b ≠ 0`: cyclic vector `(0,1)`.
      refine key 0 1 ?_
      have hval : (!![(0 : GaloisField p n), a * 0 + b * 1; 1, c * 0 + d * 1]).det = -b := by
        rw [Matrix.det_fin_two_of]; ring
      rw [hval]; exact neg_ne_zero.mpr hb0
  · -- `c ≠ 0`: cyclic vector `(1,0)`.
    refine key 1 0 ?_
    have hval : (!![(1 : GaloisField p n), a * 1 + b * 0; 0, c * 1 + d * 0]).det = c := by
      rw [Matrix.det_fin_two_of]; ring
    rw [hval]; exact hc0

/-- Two **non-scalar** `GL₂` elements with equal trace and determinant are conjugate:
both are conjugate to the same companion matrix `!![0,-det;1,tr]`. -/
private lemma isConj_of_nonscalar_tr_det {g h : GL2' p n}
    (hg : ¬ GL2.IsScalar g) (hh : ¬ GL2.IsScalar h)
    (htr : g.val 0 0 + g.val 1 1 = h.val 0 0 + h.val 1 1)
    (hdet : Matrix.det g.val = Matrix.det h.val) : IsConj g h := by
  have h1 := isConj_companion hg (g.val 0 0 + g.val 1 1) (Matrix.det g.val)
    (detval_ne_zero g) rfl rfl
  have h2 := isConj_companion hh (g.val 0 0 + g.val 1 1) (Matrix.det g.val)
    (detval_ne_zero g) htr hdet
  exact h1.trans h2.symm

/-- The **elliptic representative** `!![x, ε·y; y, x]` for a fixed non-square `ε` and
`y ≠ 0`. Its determinant `x² − ε·y²` is nonzero: otherwise `ε = (x/y)²` would be a
square. -/
noncomputable def ellipticRep (ε x y : GaloisField p n) (hε : ¬ IsSquare ε) (hy : y ≠ 0) :
    GL2' p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x, ε * y; y, x] (by
    rw [Matrix.det_fin_two_of]
    intro h0
    apply hε
    refine ⟨x * y⁻¹, ?_⟩
    field_simp
    linear_combination -h0)

@[simp] lemma ellipticRep_val (ε x y : GaloisField p n) (hε : ¬ IsSquare ε) (hy : y ≠ 0) :
    (ellipticRep ε x y hε hy).val = !![x, ε * y; y, x] := by
  simp [ellipticRep, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]

/-- **Elliptic normal form.** For any fixed non-square `ε`, every elliptic `g` is
conjugate to `!![x, ε·y; y, x]` with `y ≠ 0` (and `x = tr(g)/2`). Since the elliptic
representative has the same trace and determinant as `g` and both are non-scalar, they are
conjugate by `isConj_of_nonscalar_tr_det`. The scale `y` is found from
`IsSquare (disc·ε)` (a product of two non-squares is a square). -/
theorem exists_conj_isElliptic (hp2 : p ≠ 2) (hn : n ≠ 0) {g : GL2' p n}
    (hg : GL2.IsElliptic g) {ε : GaloisField p n} (hε : ¬ IsSquare ε) :
    ∃ (x y : GaloisField p n) (hy : y ≠ 0),
      IsConj g (ellipticRep ε x y hε hy) := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : DecidableEq (GaloisField p n) := Classical.decEq _
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h
    have hchar2 : CharP (GaloisField p n) 2 :=
      (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h
    have hp_char : CharP (GaloisField p n) p :=
      charP_of_injective_algebraMap (algebraMap (ZMod p) (GaloisField p n)).injective p
    exact hp2 (CharP.eq (GaloisField p n) hp_char hchar2)
  have h4 : (4 : GaloisField p n) ≠ 0 := by
    have : (4 : GaloisField p n) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  set a := g.val 0 0 with ha
  set b := g.val 0 1 with hb
  set c := g.val 1 0 with hc'
  set d := g.val 1 1 with hd
  set D := GL2.disc g with hDdef
  have hDsq : ¬ IsSquare D := hg
  have hDne : D ≠ 0 := fun h => hDsq (h ▸ ⟨0, by ring⟩)
  have hεne : ε ≠ 0 := fun h => hε (h ▸ ⟨0, by ring⟩)
  -- `disc · ε` is a square: product of two non-squares.
  have hχD : quadraticChar (GaloisField p n) D = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).mpr hDsq
  have hχε : quadraticChar (GaloisField p n) ε = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).mpr hε
  have hDεne : D * ε ≠ 0 := mul_ne_zero hDne hεne
  have hχDε : quadraticChar (GaloisField p n) (D * ε) = 1 := by
    rw [map_mul, hχD, hχε]; ring
  obtain ⟨z, hz⟩ := (quadraticChar_one_iff_isSquare hDεne).mp hχDε
  have hzne : z ≠ 0 := by
    intro h; apply hDεne; rw [hz, h, mul_zero]
  set x := (a + d) / 2 with hxdef
  set y := z * (2 * ε)⁻¹ with hydef
  have hx2 : 2 * x = a + d := by rw [hxdef]; field_simp
  have hy : y ≠ 0 := by
    rw [hydef]; exact mul_ne_zero hzne (inv_ne_zero (mul_ne_zero h2 hεne))
  -- `ε·y² = disc/4`, from `z² = disc·ε`.
  have hεyy : ε * y * y = D / 4 := by
    rw [hydef, eq_div_iff h4]
    field_simp
    linear_combination (-4 : GaloisField p n) * hz
  clear_value x y
  refine ⟨x, y, hy, ?_⟩
  -- `g` and the elliptic representative are non-scalar with equal trace and determinant.
  apply isConj_of_nonscalar_tr_det
  · exact fun hsc => GL2.isScalar_not_isElliptic g hsc hg
  · intro hsc
    have hy0 : (ellipticRep ε x y hε hy).val 1 0 = 0 := ((GL2.isScalar_iff _).mp hsc).2.1
    rw [ellipticRep_val] at hy0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.empty_val'] at hy0
    exact hy hy0
  · rw [ellipticRep_val]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', ← ha, ← hd]
    linear_combination -hx2
  · rw [ellipticRep_val, Matrix.det_fin_two, Matrix.det_fin_two_of, ← ha, ← hb, ← hc', ← hd]
    have hDval : D = (a - d) ^ 2 + 4 * b * c := by rw [hDdef, GL2.disc_eq, ← ha, ← hb, ← hc', ← hd]
    have hx2' : a * d - b * c = x * x - D / 4 := by
      rw [hDval]; field_simp
      linear_combination -(2 * x + a + d) * hx2
    rw [hx2', ← hεyy]

end Representatives

end GL2

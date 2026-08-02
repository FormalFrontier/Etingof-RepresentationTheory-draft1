import EtingofRepresentationTheory.Chapter2.Problem2_16_3
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.DirectSum.Decomposition


/-!
# The `ℕ²`-bidegree grading on the free Lie algebra `FreeLieAlgebra k (Fin 2)`

`EtingofRepresentationTheory/Chapter2/Problem2_16_3.lean` builds
`𝔤ₙ = FreeLieAlgebra k (Fin 2) ⧸ relIdeal k n` and the whole Chapter 2 analysis of `𝔤₄`
reasons about elements whose bidegrees — the number of `x`s and the number of `y`s in a
bracket monomial — are known on paper but invisible to Lean. This file supplies the missing
grading on the *free* Lie algebra.

## The construction

The grading is cut out by a single "scaling" Lie algebra homomorphism. Let
`degAlg k = k[ℕ × ℕ]` be the monoid algebra of the bidegree monoid, write `degMon p` for
the monomial `single p 1`, and give `degAlg k ⊗[k] FreeLieAlgebra k (Fin 2)` its base-change
Lie algebra structure (`Mathlib/Algebra/Lie/BaseChange.lean`). The universal property of the
free Lie algebra produces

`scaleHom : FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ degAlg k ⊗[k] FreeLieAlgebra k (Fin 2)`

sending `x ↦ degMon (1,0) ⊗ₜ x` and `y ↦ degMon (0,1) ⊗ₜ y`; on paper this is
`u ↦ s^(deg_x u) t^(deg_y u) ⊗ u`. Reading off the coefficient of `degMon p` gives the
projection `homogProj p` onto the bidegree-`p` part.

The homogeneous submodule `freeDeg p` is defined independently, as the span of the bracket
monomials of bidegree `p` (`IsBracketWord`). The two descriptions fit together:

* `scaleHom` is `u ↦ degMon p ⊗ₜ u` on `freeDeg p` (`scaleHom_of_mem`), which forces the
  `freeDeg p` to be independent (`iSupIndep_freeDeg`);
* the `freeDeg p` span everything (`iSup_freeDeg`), because their supremum is closed under
  the bracket and contains the generators.

Together these give `DirectSum.IsInternal (freeDeg k)` — the grading.

## Main results

* `freeDeg` : the bidegree-`p` homogeneous submodule.
* `lie_mem_freeDeg` : `⁅freeDeg p, freeDeg q⁆ ≤ freeDeg (p + q)`.
* `x_mem_freeDeg`, `y_mem_freeDeg` : the generators sit in bidegrees `(1,0)` and `(0,1)`.
* `iSup_freeDeg`, `iSupIndep_freeDeg`, `isInternal_freeDeg` : the grading.
* `homogProj` : the bidegree-`p` projection, with `homogProj_mem`,
  `homogProj_of_mem` and `exists_finset_sum_homogProj`.
-/

namespace Etingof.Problem2_16_3

open FreeLieAlgebra TensorProduct

variable (k : Type*) [CommRing k]

/-! ## The bidegree monoid algebra and the scaling homomorphism -/

/-- The monoid algebra `k[ℕ × ℕ]` of the bidegree monoid; `degMon p` is its monomial basis. -/
abbrev degAlg : Type _ := AddMonoidAlgebra k (ℕ × ℕ)

/-- The monomial `s^p.1 t^p.2` of `degAlg k = k[ℕ × ℕ]`. -/
noncomputable def degMon (p : ℕ × ℕ) : degAlg k := AddMonoidAlgebra.single p 1

/-- Coefficient or grading formula for `degMon_mul`. -/
theorem degMon_mul (p q : ℕ × ℕ) : degMon k p * degMon k q = degMon k (p + q) := by
  simp [degMon, AddMonoidAlgebra.single_mul_single]

/-- The bidegree of the `i`-th generator: `x` has bidegree `(1, 0)` and `y` has `(0, 1)`. -/
def genDeg : Fin 2 → ℕ × ℕ := ![(1, 0), (0, 1)]

/-- The zero case of `genDeg`. -/
@[simp] theorem genDeg_zero : genDeg 0 = (1, 0) := rfl
/-- The value of `genDeg` at one. -/
@[simp] theorem genDeg_one : genDeg 1 = (0, 1) := rfl

/-- The scaling homomorphism `u ↦ s^(deg_x u) t^(deg_y u) ⊗ u`, obtained from the universal
property of the free Lie algebra. It is the whole content of the grading. -/
noncomputable def scaleHom :
    FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ degAlg k ⊗[k] FreeLieAlgebra k (Fin 2) :=
  FreeLieAlgebra.lift k fun i => degMon k (genDeg i) ⊗ₜ[k] FreeLieAlgebra.of k i

/-- The scaling homomorphism formula for `scaleHom_of`. -/
@[simp] theorem scaleHom_of (i : Fin 2) :
    scaleHom k (FreeLieAlgebra.of k i) = degMon k (genDeg i) ⊗ₜ[k] FreeLieAlgebra.of k i :=
  FreeLieAlgebra.lift_of_apply _ _

/-! ## Reading off a bidegree coefficient -/

/-- The `k`-linear functional picking out the coefficient of the monomial `degMon p`. -/
noncomputable def coeffAt (p : ℕ × ℕ) : degAlg k →ₗ[k] k :=
  Finsupp.lapply p ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

/-- Coefficient or grading formula for `coeffAt_degMon`. -/
theorem coeffAt_degMon (p q : ℕ × ℕ) :
    coeffAt k p (degMon k q) = if q = p then 1 else 0 := by
  classical
  simp [coeffAt, degMon, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.single_apply]

/-- Coefficient extraction on `degAlg k ⊗[k] FreeLieAlgebra k (Fin 2)`. -/
noncomputable def tCoeff (p : ℕ × ℕ) :
    degAlg k ⊗[k] FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2) :=
  (TensorProduct.lid k (FreeLieAlgebra k (Fin 2))).toLinearMap ∘ₗ
    TensorProduct.map (coeffAt k p) LinearMap.id

/-- Coefficient or grading formula for `tCoeff_tmul`. -/
@[simp] theorem tCoeff_tmul (p : ℕ × ℕ) (a : degAlg k) (u : FreeLieAlgebra k (Fin 2)) :
    tCoeff k p (a ⊗ₜ[k] u) = coeffAt k p a • u := rfl

/-- The bidegree-`p` projection `FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2)`. -/
noncomputable def homogProj (p : ℕ × ℕ) :
    FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2) :=
  tCoeff k p ∘ₗ (scaleHom k).toLinearMap

/-- The homogeneous projection formula for `homogProj_apply`. -/
theorem homogProj_apply (p : ℕ × ℕ) (u : FreeLieAlgebra k (Fin 2)) :
    homogProj k p u = tCoeff k p (scaleHom k u) := rfl

/-! ## Bracket monomials and the homogeneous submodules -/

/-- `IsBracketWord p u` says that `u` is an iterated bracket of the generators containing
`p.1` copies of `x` and `p.2` copies of `y`. -/
inductive IsBracketWord : ℕ × ℕ → FreeLieAlgebra k (Fin 2) → Prop
  | of (i : Fin 2) : IsBracketWord (genDeg i) (FreeLieAlgebra.of k i)
  | lie {p q : ℕ × ℕ} {u v : FreeLieAlgebra k (Fin 2)} :
      IsBracketWord p u → IsBracketWord q v → IsBracketWord (p + q) ⁅u, v⁆

/-- The bidegree-`p` homogeneous submodule of `FreeLieAlgebra k (Fin 2)`: the span of the
bracket monomials with `p.1` copies of `x` and `p.2` copies of `y`. -/
noncomputable def freeDeg (p : ℕ × ℕ) : Submodule k (FreeLieAlgebra k (Fin 2)) :=
  Submodule.span k {u | IsBracketWord k p u}

/-- A bracket word belongs to its indicated free homogeneous component. -/
theorem subset_freeDeg {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : IsBracketWord k p u) :
    u ∈ freeDeg k p :=
  Submodule.subset_span h

/-- Membership statement for `of_mem_freeDeg`. -/
theorem of_mem_freeDeg (i : Fin 2) :
    FreeLieAlgebra.of k i ∈ freeDeg k (genDeg i) :=
  subset_freeDeg k (.of i)

/-- The corresponding generator belongs to its indicated homogeneous component. -/
theorem x_mem_freeDeg : x k ∈ freeDeg k (1, 0) := of_mem_freeDeg k 0

/-- The corresponding generator belongs to its indicated homogeneous component. -/
theorem y_mem_freeDeg : y k ∈ freeDeg k (0, 1) := of_mem_freeDeg k 1

/-- Bracket additivity of the bidegree. -/
theorem lie_mem_freeDeg {p q : ℕ × ℕ} {u v : FreeLieAlgebra k (Fin 2)}
    (hu : u ∈ freeDeg k p) (hv : v ∈ freeDeg k q) : ⁅u, v⁆ ∈ freeDeg k (p + q) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      induction hv using Submodule.span_induction with
      | mem v hv => exact subset_freeDeg k (hu.lie hv)
      | zero => simp
      | add v w _ _ hv hw => simpa [lie_add] using (freeDeg k (p + q)).add_mem hv hw
      | smul c v _ hv => simpa [lie_smul] using (freeDeg k (p + q)).smul_mem c hv
  | zero => simp
  | add u w _ _ hu hw => simpa [add_lie] using (freeDeg k (p + q)).add_mem hu hw
  | smul c u _ hu => simpa [smul_lie] using (freeDeg k (p + q)).smul_mem c hu

/-! ## `scaleHom` on homogeneous elements -/

/-- The scaling homomorphism formula for `scaleHom_of_isBracketWord`. -/
theorem scaleHom_of_isBracketWord {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : IsBracketWord k p u) : scaleHom k u = degMon k p ⊗ₜ[k] u := by
  induction h with
  | of i => exact scaleHom_of k i
  | @lie p q u v _ _ hu hv =>
      rw [LieHom.map_lie, hu, hv, LieAlgebra.ExtendScalars.bracket_tmul, degMon_mul]

/-- The scaling homomorphism formula for `scaleHom_of_mem`. -/
theorem scaleHom_of_mem {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : u ∈ freeDeg k p) :
    scaleHom k u = degMon k p ⊗ₜ[k] u := by
  induction h using Submodule.span_induction with
  | mem u hu => exact scaleHom_of_isBracketWord k hu
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, hu, hv, TensorProduct.tmul_add]
  | smul c u _ hu => rw [map_smul, hu, TensorProduct.tmul_smul]

/-- The projections are orthogonal idempotents in the strong sense: on a homogeneous element
of bidegree `p`, `homogProj p` is the identity and every other `homogProj q` vanishes. -/
theorem homogProj_of_mem {p q : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : u ∈ freeDeg k p) :
    homogProj k q u = if p = q then u else 0 := by
  classical
  rw [homogProj_apply, scaleHom_of_mem k h, tCoeff_tmul, coeffAt_degMon]
  split <;> simp

/-- The homogeneous projection formula for `homogProj_self_of_mem`. -/
theorem homogProj_self_of_mem {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : u ∈ freeDeg k p) : homogProj k p u = u := by
  simp [homogProj_of_mem k h]

/-- The homogeneous projection formula for `homogProj_eq_zero_of_mem`. -/
theorem homogProj_eq_zero_of_mem {p q : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : u ∈ freeDeg k p) (hpq : p ≠ q) : homogProj k q u = 0 := by
  simp [homogProj_of_mem k h, hpq]

/-! ## The grading -/

/-- The homogeneous submodules span: their supremum is closed under the bracket and contains
the generators, so it is all of the free Lie algebra. -/
theorem iSup_freeDeg : ⨆ p : ℕ × ℕ, freeDeg k p = ⊤ := by
  set S : Submodule k (FreeLieAlgebra k (Fin 2)) := ⨆ p : ℕ × ℕ, freeDeg k p with hS
  have hmem : ∀ (p : ℕ × ℕ) {u}, u ∈ freeDeg k p → u ∈ S := fun p _ hu =>
    (le_iSup (fun p : ℕ × ℕ => freeDeg k p) p) hu
  -- `S` is a Lie subalgebra.
  have hlie : ∀ u ∈ S, ∀ v ∈ S, ⁅u, v⁆ ∈ S := by
    intro u hu v hv
    induction hu using Submodule.iSup_induction' with
    | mem p u hu =>
        induction hv using Submodule.iSup_induction' with
        | mem q v hv => exact hmem (p + q) (lie_mem_freeDeg k hu hv)
        | zero => simp
        | add v w _ _ hv hw => simpa [lie_add] using S.add_mem hv hw
    | zero => simp
    | add u w _ _ hu hw => simpa [add_lie] using S.add_mem hu hw
  let H : LieSubalgebra k (FreeLieAlgebra k (Fin 2)) :=
    { S with lie_mem' := fun {u v} hu hv => hlie u hu v hv }
  have hgen : Set.range (FreeLieAlgebra.of k) ⊆ (H : Set (FreeLieAlgebra k (Fin 2))) := by
    rintro _ ⟨i, rfl⟩
    exact hmem (genDeg i) (of_mem_freeDeg k i)
  have : (⊤ : LieSubalgebra k (FreeLieAlgebra k (Fin 2))) ≤ H := by
    rw [← lieSpan_range_of_eq_top k]
    exact LieSubalgebra.lieSpan_le.2 hgen
  rw [eq_top_iff]
  intro u _
  exact this (LieSubalgebra.mem_top u)

/-- The homogeneous projection formula for `homogProj_mem`. -/
theorem homogProj_mem (p : ℕ × ℕ) (u : FreeLieAlgebra k (Fin 2)) :
    homogProj k p u ∈ freeDeg k p := by
  have hu : u ∈ ⨆ q : ℕ × ℕ, freeDeg k q := by rw [iSup_freeDeg]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem q v hv =>
      rw [homogProj_of_mem k hv]
      split
      · subst ‹q = p›; exact hv
      · exact (freeDeg k p).zero_mem
  | zero => simp
  | add v w _ _ hv hw => simpa using (freeDeg k p).add_mem hv hw

/-- Every element has a finite bidegree decomposition, recovered by the projections. -/
theorem exists_finset_sum_homogProj (u : FreeLieAlgebra k (Fin 2)) :
    ∃ s : Finset (ℕ × ℕ), (∀ p ∉ s, homogProj k p u = 0) ∧ ∑ p ∈ s, homogProj k p u = u := by
  classical
  have hu : u ∈ ⨆ q : ℕ × ℕ, freeDeg k q := by rw [iSup_freeDeg]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem q v hv =>
      refine ⟨{q}, fun p hp => homogProj_eq_zero_of_mem k hv (Ne.symm (by simpa using hp)), ?_⟩
      simp [homogProj_self_of_mem k hv]
  | zero => exact ⟨∅, by simp, by simp⟩
  | add v w _ _ hv hw =>
      obtain ⟨s, hs0, hs⟩ := hv
      obtain ⟨t, ht0, ht⟩ := hw
      refine ⟨s ∪ t, fun p hp => by simp [hs0 p (fun h => hp (Finset.mem_union_left _ h)),
        ht0 p (fun h => hp (Finset.mem_union_right _ h))], ?_⟩
      have hs' : ∑ p ∈ s ∪ t, homogProj k p v = v :=
        (Finset.sum_subset Finset.subset_union_left (fun p _ hp => hs0 p hp)).symm.trans hs
      have ht' : ∑ p ∈ s ∪ t, homogProj k p w = w :=
        (Finset.sum_subset Finset.subset_union_right (fun p _ hp => ht0 p hp)).symm.trans ht
      simp only [map_add, Finset.sum_add_distrib, hs', ht']

/-- A sum of homogeneous pieces of bidegree different from `p` has vanishing `p`-component. -/
theorem homogProj_eq_zero_of_mem_iSup_ne {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (hu : u ∈ ⨆ q, ⨆ (_ : q ≠ p), freeDeg k q) : homogProj k p u = 0 := by
  induction hu using Submodule.iSup_induction' with
  | mem q v hv =>
      by_cases hq : q = p
      · subst hq
        rw [iSup_neg (by simp)] at hv
        simp [(Submodule.mem_bot k).1 hv]
      · rw [iSup_pos hq] at hv
        exact homogProj_eq_zero_of_mem k hv hq
  | zero => simp
  | add v w _ _ hv hw => simp [hv, hw]

/-- Direct-sum identity for `iSupIndep_freeDeg`. -/
theorem iSupIndep_freeDeg : iSupIndep (freeDeg k) := by
  intro p
  rw [Submodule.disjoint_def]
  intro u hu hu'
  rw [← homogProj_self_of_mem k hu, homogProj_eq_zero_of_mem_iSup_ne k hu']

/-- **The `ℕ²`-bidegree grading on `FreeLieAlgebra k (Fin 2)`.** -/
theorem isInternal_freeDeg : DirectSum.IsInternal (freeDeg k) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_freeDeg k, iSup_freeDeg k⟩

/-- The grading, packaged as a `DirectSum.Decomposition` instance. -/
noncomputable instance freeDegDecomposition : DirectSum.Decomposition (freeDeg k) :=
  (isInternal_freeDeg k).chooseDecomposition

/-! ## The relator ideal is homogeneous

Both defining relators are bihomogeneous — `⁅x, ⁅x, y⁆⁆` has bidegree `(2, 1)` and
`ad(y)ⁿ⁺¹ x` has bidegree `(1, n + 1)` — and the Lie ideal generated by homogeneous elements
is homogeneous. -/

/-- The defining relator belongs to the indicated homogeneous component. -/
theorem relator1_mem_freeDeg : ⁅x k, ⁅x k, y k⁆⁆ ∈ freeDeg k (2, 1) := by
  have hdeg : ((1, 0) + ((1, 0) + (0, 1)) : ℕ × ℕ) = (2, 1) := rfl
  exact hdeg ▸
    lie_mem_freeDeg k (x_mem_freeDeg k) (lie_mem_freeDeg k (x_mem_freeDeg k) (y_mem_freeDeg k))

/-- The defining relator belongs to the indicated homogeneous component. -/
theorem relator2_mem_freeDeg (n : ℕ) :
    (fun z => ⁅y k, z⁆)^[n + 1] (x k) ∈ freeDeg k (1, n + 1) := by
  induction n with
  | zero => simpa using lie_mem_freeDeg k (y_mem_freeDeg k) (x_mem_freeDeg k)
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simpa [Prod.ext_iff, add_comm] using lie_mem_freeDeg k (y_mem_freeDeg k) ih

/-- The Lie ideal of elements all of whose bidegree components lie in `relIdeal k n`. It
contains the relators, hence contains — and therefore equals — `relIdeal k n` itself. -/
noncomputable def relIdealHomog (n : ℕ) : LieIdeal k (FreeLieAlgebra k (Fin 2)) where
  carrier := {u | ∀ p, homogProj k p u ∈ relIdeal k n}
  add_mem' hu hv p := by simpa using (relIdeal k n).add_mem (hu p) (hv p)
  zero_mem' p := by simp
  smul_mem' c _ hu p := by simpa using (relIdeal k n).smul_mem c (hu p)
  lie_mem {v u} hu p := by
    classical
    obtain ⟨s, _, hs⟩ := exists_finset_sum_homogProj k v
    obtain ⟨t, _, ht⟩ := exists_finset_sum_homogProj k u
    have hvu : ⁅v, u⁆ = ∑ q ∈ s, ∑ r ∈ t, ⁅homogProj k q v, homogProj k r u⁆ := by
      conv_lhs => rw [← hs, ← ht]
      exact sum_lie_sum _ _ _ _
    rw [hvu, map_sum]
    refine (relIdeal k n).sum_mem fun q _ => ?_
    rw [map_sum]
    refine (relIdeal k n).sum_mem fun r _ => ?_
    have hmem : ⁅homogProj k q v, homogProj k r u⁆ ∈ freeDeg k (q + r) :=
      lie_mem_freeDeg k (homogProj_mem k q v) (homogProj_mem k r u)
    rw [homogProj_of_mem k hmem]
    split
    · exact (relIdeal k n).lie_mem (hu r)
    · exact (relIdeal k n).zero_mem

/-- **`relIdeal k n` is homogeneous for the bidegree grading.** -/
theorem homogProj_mem_relIdeal {n : ℕ} {u : FreeLieAlgebra k (Fin 2)} (hu : u ∈ relIdeal k n)
    (p : ℕ × ℕ) : homogProj k p u ∈ relIdeal k n := by
  have hle : relIdeal k n ≤ relIdealHomog k n := by
    rw [relIdeal, LieSubmodule.lieSpan_le]
    rintro a (rfl | rfl) q
    · rw [homogProj_of_mem k (relator1_mem_freeDeg k)]
      split
      · exact LieSubmodule.subset_lieSpan (by simp)
      · exact (relIdeal k n).zero_mem
    · rw [homogProj_of_mem k (relator2_mem_freeDeg k n)]
      split
      · exact LieSubmodule.subset_lieSpan (by simp)
      · exact (relIdeal k n).zero_mem
  exact hle hu p

/-! ## The induced grading on `𝔤ₙ` -/

/-- The bidegree-`p` homogeneous submodule of `𝔤ₙ`, the image of `freeDeg k p`. -/
noncomputable def gDeg (n : ℕ) (p : ℕ × ℕ) : Submodule k (g k n) :=
  (freeDeg k p).map (proj k n).toLinearMap

/-- Membership statement for `proj_mem_gDeg`. -/
theorem proj_mem_gDeg {n : ℕ} {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (hu : u ∈ freeDeg k p) :
    proj k n u ∈ gDeg k n p :=
  ⟨u, hu, rfl⟩

/-- Membership in a quotient homogeneous component is characterized by a homogeneous lift. -/
theorem mem_gDeg_iff {n : ℕ} {p : ℕ × ℕ} {a : g k n} :
    a ∈ gDeg k n p ↔ ∃ u ∈ freeDeg k p, proj k n u = a := Iff.rfl

/-- The corresponding generator belongs to its indicated homogeneous component. -/
theorem xb_mem_gDeg (n : ℕ) : xb k n ∈ gDeg k n (1, 0) := proj_mem_gDeg k (x_mem_freeDeg k)

/-- The corresponding generator belongs to its indicated homogeneous component. -/
theorem yb_mem_gDeg (n : ℕ) : yb k n ∈ gDeg k n (0, 1) := proj_mem_gDeg k (y_mem_freeDeg k)

/-- Bracket additivity of the bidegree on `𝔤ₙ`. -/
theorem lie_mem_gDeg {n : ℕ} {p q : ℕ × ℕ} {a b : g k n} (ha : a ∈ gDeg k n p)
    (hb : b ∈ gDeg k n q) : ⁅a, b⁆ ∈ gDeg k n (p + q) := by
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  exact ⟨⁅u, v⁆, lie_mem_freeDeg k hu hv, by simp⟩

/-- The bidegree-`p` projection on `𝔤ₙ`, induced by `homogProj` through the homogeneity of
`relIdeal k n`. -/
noncomputable def gProj (n : ℕ) (p : ℕ × ℕ) : g k n →ₗ[k] g k n :=
  Submodule.liftQ (relIdeal k n).toSubmodule ((proj k n).toLinearMap ∘ₗ homogProj k p)
    (by
      intro a ha
      have : homogProj k p a ∈ relIdeal k n := homogProj_mem_relIdeal k ha p
      simpa using ((proj_eq_zero_iff k n _).2 this))

/-- The graded projection formula for `gProj_proj`. -/
theorem gProj_proj (n : ℕ) (p : ℕ × ℕ) (u : FreeLieAlgebra k (Fin 2)) :
    gProj k n p (proj k n u) = proj k n (homogProj k p u) := rfl

/-- The graded projection formula for `gProj_of_mem`. -/
theorem gProj_of_mem {n : ℕ} {p q : ℕ × ℕ} {a : g k n} (ha : a ∈ gDeg k n p) :
    gProj k n q a = if p = q then a else 0 := by
  obtain ⟨u, hu, rfl⟩ := ha
  change gProj k n q (proj k n u) = if p = q then proj k n u else 0
  rw [gProj_proj, homogProj_of_mem k hu]
  split
  · simp
  · rfl

/-- The graded projection formula for `gProj_self_of_mem`. -/
theorem gProj_self_of_mem {n : ℕ} {p : ℕ × ℕ} {a : g k n} (ha : a ∈ gDeg k n p) :
    gProj k n p a = a := by simp [gProj_of_mem k ha]

/-- The graded projection formula for `gProj_mem`. -/
theorem gProj_mem (n : ℕ) (p : ℕ × ℕ) (a : g k n) : gProj k n p a ∈ gDeg k n p := by
  obtain ⟨u, rfl⟩ := proj_surjective k n a
  rw [gProj_proj]
  exact proj_mem_gDeg k (homogProj_mem k p u)

/-- The bidegree-`p` projection has image exactly the bidegree-`p` component. -/
theorem range_gProj (n : ℕ) (p : ℕ × ℕ) : LinearMap.range (gProj k n p) = gDeg k n p := by
  refine le_antisymm ?_ fun a ha => ⟨a, gProj_self_of_mem k ha⟩
  rintro _ ⟨a, rfl⟩
  exact gProj_mem k n p a

/-- **A spanning set of `𝔤ₙ` induces a spanning set of every bidegree component**, by projecting
it. This is the tool that turns a global spanning family into bidegree-wise upper bounds. -/
theorem gDeg_eq_span_image {n : ℕ} (p : ℕ × ℕ) {S : Set (g k n)} (hS : Submodule.span k S = ⊤) :
    gDeg k n p = Submodule.span k (gProj k n p '' S) := by
  rw [← range_gProj k n p, ← Submodule.map_top, ← hS, Submodule.map_span]

/-- The graded projection formula for `gProj_eq_zero_of_mem`. -/
theorem gProj_eq_zero_of_mem {n : ℕ} {p q : ℕ × ℕ} {a : g k n} (ha : a ∈ gDeg k n p)
    (hpq : p ≠ q) : gProj k n q a = 0 := by simp [gProj_of_mem k ha, hpq]

/-- Direct-sum identity for `iSup_gDeg`. -/
theorem iSup_gDeg (n : ℕ) : ⨆ p : ℕ × ℕ, gDeg k n p = ⊤ := by
  have hmap : ⨆ p : ℕ × ℕ, gDeg k n p
      = (⨆ p : ℕ × ℕ, freeDeg k p).map (proj k n).toLinearMap :=
    (Submodule.map_iSup _ _).symm
  have hsurj : Function.Surjective ⇑(proj k n).toLinearMap := proj_surjective k n
  rw [hmap, iSup_freeDeg, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

/-- The graded projection formula for `gProj_eq_zero_of_mem_iSup_ne`. -/
theorem gProj_eq_zero_of_mem_iSup_ne {n : ℕ} {p : ℕ × ℕ} {a : g k n}
    (ha : a ∈ ⨆ q, ⨆ (_ : q ≠ p), gDeg k n q) : gProj k n p a = 0 := by
  induction ha using Submodule.iSup_induction' with
  | mem q b hb =>
      by_cases hq : q = p
      · subst hq
        rw [iSup_neg (by simp)] at hb
        simp [(Submodule.mem_bot k).1 hb]
      · rw [iSup_pos hq] at hb
        exact gProj_eq_zero_of_mem k hb hq
  | zero => simp
  | add b c _ _ hb hc => simp [hb, hc]

/-- Direct-sum identity for `iSupIndep_gDeg`. -/
theorem iSupIndep_gDeg (n : ℕ) : iSupIndep (gDeg k n) := by
  intro p
  rw [Submodule.disjoint_def]
  intro a ha ha'
  rw [← gProj_self_of_mem k ha, gProj_eq_zero_of_mem_iSup_ne k ha']

/-- **The `ℕ²`-bidegree grading on `𝔤ₙ = FreeLieAlgebra k (Fin 2) ⧸ relIdeal k n`.** -/
theorem isInternal_gDeg (n : ℕ) : DirectSum.IsInternal (gDeg k n) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_gDeg k n, iSup_gDeg k n⟩

/-- The quotient grading, packaged as a `DirectSum.Decomposition` instance. -/
noncomputable instance gDegDecomposition (n : ℕ) : DirectSum.Decomposition (gDeg k n) :=
  (isInternal_gDeg k n).chooseDecomposition

/-! ## Bidegrees of the Chapter 2 vocabulary -/

/-- `aᵢ = ad(ȳ)ⁱ(x̄)` has bidegree `(1, i)`. -/
theorem aElt_mem_gDeg (n i : ℕ) : aElt k n i ∈ gDeg k n (1, i) := by
  induction i with
  | zero => simpa using xb_mem_gDeg k n
  | succ i ih =>
      rw [aElt_succ]
      simpa [Prod.ext_iff, add_comm] using lie_mem_gDeg k (yb_mem_gDeg k n) ih

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.degAlg
  Etingof.Problem2_16_3.degMon
  Etingof.Problem2_16_3.genDeg
  Etingof.Problem2_16_3.scaleHom
  Etingof.Problem2_16_3.coeffAt
  Etingof.Problem2_16_3.tCoeff
  Etingof.Problem2_16_3.homogProj
  Etingof.Problem2_16_3.freeDeg
  Etingof.Problem2_16_3.freeDegDecomposition
  Etingof.Problem2_16_3.relIdealHomog
  Etingof.Problem2_16_3.gDeg
  Etingof.Problem2_16_3.gProj
  Etingof.Problem2_16_3.gDegDecomposition

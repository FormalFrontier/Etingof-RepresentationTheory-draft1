import EtingofRepresentationTheory.Chapter2.Problem2_16_3
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.MonoidAlgebra.Module
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

theorem degMon_mul (p q : ℕ × ℕ) : degMon k p * degMon k q = degMon k (p + q) := by
  simp [degMon, AddMonoidAlgebra.single_mul_single]

/-- The bidegree of the `i`-th generator: `x` has bidegree `(1, 0)` and `y` has `(0, 1)`. -/
def genDeg : Fin 2 → ℕ × ℕ := ![(1, 0), (0, 1)]

@[simp] theorem genDeg_zero : genDeg 0 = (1, 0) := rfl
@[simp] theorem genDeg_one : genDeg 1 = (0, 1) := rfl

/-- The scaling homomorphism `u ↦ s^(deg_x u) t^(deg_y u) ⊗ u`, obtained from the universal
property of the free Lie algebra. It is the whole content of the grading. -/
noncomputable def scaleHom :
    FreeLieAlgebra k (Fin 2) →ₗ⁅k⁆ degAlg k ⊗[k] FreeLieAlgebra k (Fin 2) :=
  FreeLieAlgebra.lift k fun i => degMon k (genDeg i) ⊗ₜ[k] FreeLieAlgebra.of k i

@[simp] theorem scaleHom_of (i : Fin 2) :
    scaleHom k (FreeLieAlgebra.of k i) = degMon k (genDeg i) ⊗ₜ[k] FreeLieAlgebra.of k i :=
  FreeLieAlgebra.lift_of_apply _ _

/-! ## Reading off a bidegree coefficient -/

/-- The `k`-linear functional picking out the coefficient of the monomial `degMon p`. -/
noncomputable def coeffAt (p : ℕ × ℕ) : degAlg k →ₗ[k] k :=
  Finsupp.lapply p ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem coeffAt_degMon (p q : ℕ × ℕ) :
    coeffAt k p (degMon k q) = if q = p then 1 else 0 := by
  classical
  simp [coeffAt, degMon, AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff,
    Finsupp.single_apply]

/-- Coefficient extraction on `degAlg k ⊗[k] FreeLieAlgebra k (Fin 2)`. -/
noncomputable def tCoeff (p : ℕ × ℕ) :
    degAlg k ⊗[k] FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2) :=
  (TensorProduct.lid k (FreeLieAlgebra k (Fin 2))).toLinearMap ∘ₗ
    TensorProduct.map (coeffAt k p) LinearMap.id

@[simp] theorem tCoeff_tmul (p : ℕ × ℕ) (a : degAlg k) (u : FreeLieAlgebra k (Fin 2)) :
    tCoeff k p (a ⊗ₜ[k] u) = coeffAt k p a • u := rfl

/-- The bidegree-`p` projection `FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2)`. -/
noncomputable def homogProj (p : ℕ × ℕ) :
    FreeLieAlgebra k (Fin 2) →ₗ[k] FreeLieAlgebra k (Fin 2) :=
  tCoeff k p ∘ₗ (scaleHom k).toLinearMap

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

theorem subset_freeDeg {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)} (h : IsBracketWord k p u) :
    u ∈ freeDeg k p :=
  Submodule.subset_span h

theorem of_mem_freeDeg (i : Fin 2) :
    FreeLieAlgebra.of k i ∈ freeDeg k (genDeg i) :=
  subset_freeDeg k (.of i)

theorem x_mem_freeDeg : x k ∈ freeDeg k (1, 0) := of_mem_freeDeg k 0

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

theorem scaleHom_of_isBracketWord {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : IsBracketWord k p u) : scaleHom k u = degMon k p ⊗ₜ[k] u := by
  induction h with
  | of i => exact scaleHom_of k i
  | @lie p q u v _ _ hu hv =>
      rw [LieHom.map_lie, hu, hv, LieAlgebra.ExtendScalars.bracket_tmul, degMon_mul]

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

theorem homogProj_self_of_mem {p : ℕ × ℕ} {u : FreeLieAlgebra k (Fin 2)}
    (h : u ∈ freeDeg k p) : homogProj k p u = u := by
  simp [homogProj_of_mem k h]

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

end Etingof.Problem2_16_3

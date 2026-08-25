/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.Central.Matrix
import RepresentationTheory.Alignment.Attribute


namespace RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (B : LinearMap.BilinForm ℂ V)


/-- The quadratic form obtained by evaluating a complex bilinear form on the same vector twice. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable abbrev quadraticForm : QuadraticForm ℂ V :=
  LinearMap.BilinMap.toQuadraticMap B


/-- The complex Clifford algebra associated with the quadratic form obtained from a bilinear form. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
abbrev BilinearCliffordAlgebra : Type _ := CliffordAlgebra (quadraticForm B)


/-- The Clifford algebra of a finite-dimensional complex vector space is finite as a complex module. -/
instance moduleFinite : Module.Finite ℂ (BilinearCliffordAlgebra B) := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  haveI : Module.Finite ℂ (ExteriorAlgebra ℂ V) :=
    Module.Finite.of_basis (Module.Basis.ExteriorAlgebra (Module.finBasis ℂ V))
  exact Module.Finite.equiv (CliffordAlgebra.equivExterior (quadraticForm B)).symm

omit [FiniteDimensional ℂ V] in

/-- The Clifford algebra of the zero quadratic form is nonempty algebra-equivalent to the exterior algebra. -/
@[source_ref "Chapter3/Problem3.9.5" (role := primary)]
theorem nonempty_algEquiv_exterior_of_zero :
    Nonempty (CliffordAlgebra (quadraticForm (0 : LinearMap.BilinForm ℂ V)) ≃ₐ[ℂ]
      ExteriorAlgebra ℂ V) := by


  have hq : quadraticForm (0 : LinearMap.BilinForm ℂ V) = (0 : QuadraticForm ℂ V) := by
    ext v
    simp [quadraticForm]
  rw [hq]
  exact ⟨AlgEquiv.refl⟩


/-- A finite complex algebra is semisimple when the trace pairing defined by left multiplication is nondegenerate. -/
theorem isSemisimpleRing_of_trace_mulLeft_nondegenerate
    {A : Type*} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A]
    (hnd : ∀ x : A, (∀ y : A, LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (x * y)) = 0) → x = 0) :
    IsSemisimpleRing A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply hnd
  intro y

  have hsymm : LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (x * y))
      = LinearMap.trace ℂ A (LinearMap.mulLeft ℂ (y * x)) := by
    rw [LinearMap.mulLeft_mul, LinearMap.mulLeft_mul,
      ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, LinearMap.trace_mul_comm]
  rw [hsymm]

  have hyx : y * x ∈ Ring.jacobson A := (Ring.jacobson A).mul_mem_left y hx
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [Ideal.jacobson_bot] at hn
  have hnil : IsNilpotent (y * x) := by
    refine ⟨n, ?_⟩
    have hmem : (y * x) ^ n ∈ (Ring.jacobson A) ^ n := Ideal.pow_mem_pow hyx n
    rw [hn] at hmem
    simpa using hmem

  have hmul : IsNilpotent (LinearMap.mulLeft ℂ (y * x)) :=
    hnil.map (Algebra.lmul ℂ A).toRingHom
  exact (LinearMap.isNilpotent_trace_of_isNilpotent hmul).eq_zero


section Monomial

variable {N : ℕ} (v : Module.Basis (Fin N) ℂ V)

open CliffordAlgebra in

/-- The Clifford-algebra generator corresponding to a vector of a chosen basis. -/
noncomputable def basisGenerator (i : Fin N) : BilinearCliffordAlgebra B := CliffordAlgebra.ι (quadraticForm B) (v i)

open scoped Classical in

/-- The ordered product in the Clifford algebra associated with a finite subset of basis indices. -/
noncomputable def basisMonomial (S : Finset (Fin N)) : BilinearCliffordAlgebra B :=
  ((S.sort (· ≤ ·)).map (basisGenerator B v)).prod

omit [FiniteDimensional ℂ V] in
/-- The monomial associated with the empty subset is one. -/
@[simp] theorem basisMonomial_empty : basisMonomial B v ∅ = 1 := by
  simp [basisMonomial]

omit [FiniteDimensional ℂ V] in
/-- The monomial of a singleton is the corresponding Clifford generator. -/
@[simp] theorem basisMonomial_singleton (i : Fin N) : basisMonomial B v {i} = basisGenerator B v i := by
  simp [basisMonomial, Finset.sort_singleton]

omit [FiniteDimensional ℂ V] in


/-- Inserting an index smaller than every existing index multiplies the corresponding generator on the left of the monomial. -/
theorem basisMonomial_insert_of_lt {i : Fin N} {S : Finset (Fin N)} (h : ∀ j ∈ S, i < j) :
    basisMonomial B v (insert i S) = basisGenerator B v i * basisMonomial B v S := by
  have hi : i ∉ S := fun hmem => (lt_irrefl i (h i hmem))
  rw [basisMonomial, Finset.sort_insert (· ≤ ·) (fun j hj => (h j hj).le) hi, List.map_cons, List.prod_cons, basisMonomial]

omit [FiniteDimensional ℂ V] in

/-- A nonempty basis monomial is its least-index generator multiplied by the monomial with that index erased. -/
theorem basisMonomial_eq_min_mul_erase {S : Finset (Fin N)} (hS : S.Nonempty) :
    basisMonomial B v S = basisGenerator B v (S.min' hS) * basisMonomial B v (S.erase (S.min' hS)) := by
  have hmem : S.min' hS ∈ S := S.min'_mem hS
  have hlt : ∀ j ∈ S.erase (S.min' hS), S.min' hS < j := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact lt_of_le_of_ne (S.min'_le j hj.2) (Ne.symm hj.1)
  conv_lhs => rw [← Finset.insert_erase hmem]
  exact basisMonomial_insert_of_lt B v hlt

omit [FiniteDimensional ℂ V] in

/-- The square of a basis generator is the scalar given by the self-pairing of the corresponding basis vector. -/
theorem basisGenerator_sq (i : Fin N) :
    basisGenerator B v i * basisGenerator B v i = algebraMap ℂ (BilinearCliffordAlgebra B) (B (v i) (v i)) := by
  unfold basisGenerator
  rw [CliffordAlgebra.ι_sq_scalar]
  rfl

omit [FiniteDimensional ℂ V] in

/-- Distinct generators from an orthogonal basis anticommute. -/
theorem basisGenerator_mul_eq_neg_mul (hv : B.IsOrthoᵢ v) {i j : Fin N} (hij : i ≠ j) :
    basisGenerator B v i * basisGenerator B v j = - (basisGenerator B v j * basisGenerator B v i) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := quadraticForm B) (v i) (v j)
  have hpolar : QuadraticMap.polar (quadraticForm B) (v i) (v j) = 0 := by
    rw [LinearMap.BilinMap.polar_toQuadraticMap,
      LinearMap.isOrthoᵢ_def.mp hv i j hij, LinearMap.isOrthoᵢ_def.mp hv j i hij.symm, add_zero]
  rw [hpolar, map_zero] at h
  unfold basisGenerator
  exact eq_neg_of_add_eq_zero_left h

omit [FiniteDimensional ℂ V] in

/-- Every vector in an orthogonal basis has nonzero self-pairing for a nondegenerate bilinear form. -/
theorem bilin_self_ne_zero_of_orthogonal_nondegenerate (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (i : Fin N) :
    B (v i) (v i) ≠ 0 := by
  intro hz
  refine v.ne_zero i (hnd.1 (v i) ?_)
  intro y
  have hzero : B (v i) = 0 := by
    apply v.ext
    intro j
    rcases eq_or_ne i j with rfl | hij
    · simpa using hz
    · simpa using LinearMap.isOrthoᵢ_def.mp hv i j hij
  rw [hzero, LinearMap.zero_apply]

omit [FiniteDimensional ℂ V] in

/-- Every generator from a nondegenerate orthogonal basis is a unit in the Clifford algebra. -/
theorem isUnit_basisGenerator (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (i : Fin N) :
    IsUnit (basisGenerator B v i) := by
  have ha := bilin_self_ne_zero_of_orthogonal_nondegenerate B v hv hnd i
  refine ⟨⟨basisGenerator B v i, (B (v i) (v i))⁻¹ • basisGenerator B v i, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, basisGenerator_sq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ ha, map_one]
  · rw [smul_mul_assoc, basisGenerator_sq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ ha, map_one]

omit [FiniteDimensional ℂ V] in
open scoped Classical in

/-- Every monomial of a nondegenerate orthogonal basis is a unit in the Clifford algebra. -/
theorem isUnit_basisMonomial (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (S : Finset (Fin N)) :
    IsUnit (basisMonomial B v S) := by
  rw [basisMonomial]
  apply List.prod_isUnit
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact isUnit_basisGenerator B v hv hnd i

open scoped symmDiff

omit [FiniteDimensional ℂ V] in


/-- The product of a basis generator with a basis monomial lies in the span of the monomial indexed by the corresponding symmetric difference. -/
theorem basisGenerator_mul_mem_span_symmDiff (hv : B.IsOrthoᵢ v) (j : Fin N) (U : Finset (Fin N)) :
    basisGenerator B v j * basisMonomial B v U ∈ Submodule.span ℂ {basisMonomial B v (U ∆ {j})} := by
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    rcases U.eq_empty_or_nonempty with rfl | hU
    · have h0 : (∅ : Finset (Fin N)) ∆ {j} = {j} := by ext a; simp [Finset.mem_symmDiff]
      rw [basisMonomial_empty, mul_one, h0, basisMonomial_singleton]
      exact Submodule.mem_span_singleton_self _
    · rcases lt_trichotomy j (U.min' hU) with hjk | hjk | hjk
      ·
        have hjnotU : j ∉ U := fun hmem => absurd (U.min'_le j hmem) (not_le.mpr hjk)
        have hlt : ∀ i ∈ U, j < i := fun i hi => lt_of_lt_of_le hjk (U.min'_le i hi)
        have hset : U ∆ {j} = insert j U := by
          ext a
          simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
          constructor
          · rintro (⟨ha, _⟩ | ⟨rfl, _⟩)
            · exact Or.inr ha
            · exact Or.inl rfl
          · rintro (rfl | ha)
            · exact Or.inr ⟨rfl, hjnotU⟩
            · exact Or.inl ⟨ha, fun h => hjnotU (h ▸ ha)⟩
        rw [hset, ← basisMonomial_insert_of_lt B v hlt]
        exact Submodule.mem_span_singleton_self _
      ·
        have hjU : j ∈ U := hjk ▸ U.min'_mem hU
        have hset : U ∆ {j} = U.erase j := by
          ext a
          simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
          constructor
          · rintro (⟨ha, hne⟩ | ⟨rfl, hn⟩)
            · exact ⟨hne, ha⟩
            · exact absurd hjU hn
          · rintro ⟨hne, ha⟩; exact Or.inl ⟨ha, hne⟩
        rw [hset, basisMonomial_eq_min_mul_erase B v hU, ← hjk, ← mul_assoc, basisGenerator_sq, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      ·
        set k := U.min' hU with hkdef
        have hkU : k ∈ U := U.min'_mem hU
        have hjne : j ≠ k := ne_of_gt hjk
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
          (ih (U.erase k) (Finset.erase_ssubset hkU))
        have hltW : ∀ i ∈ (U.erase k) ∆ {j}, k < i := by
          intro i hi
          simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton] at hi
          rcases hi with ⟨⟨hik, hiU⟩, _⟩ | ⟨rfl, _⟩
          · have hle : k ≤ i := U.min'_le i hiU
            exact lt_of_le_of_ne hle (Ne.symm hik)
          · exact hjk
        have hset : insert k ((U.erase k) ∆ {j}) = U ∆ {j} := by
          ext a
          simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_erase,
            Finset.mem_singleton]
          by_cases hak : a = k <;> by_cases haj : a = j <;> by_cases haU : a ∈ U <;>
            simp_all
        rw [basisMonomial_eq_min_mul_erase B v hU, ← hkdef, ← mul_assoc, basisGenerator_mul_eq_neg_mul B v hv hjne, neg_mul,
          mul_assoc, ← hc, mul_smul_comm, ← basisMonomial_insert_of_lt B v hltW, hset]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

omit [FiniteDimensional ℂ V] in


/-- The product of two orthogonal-basis monomials lies in the span of the monomial indexed by their symmetric difference. -/
theorem basisMonomial_mul_mem_span_symmDiff (hv : B.IsOrthoᵢ v) (S T : Finset (Fin N)) :
    basisMonomial B v S * basisMonomial B v T ∈ Submodule.span ℂ {basisMonomial B v (S ∆ T)} := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · have h0 : (∅ : Finset (Fin N)) ∆ T = T := by ext a; simp [Finset.mem_symmDiff]
      rw [basisMonomial_empty, one_mul, h0]
      exact Submodule.mem_span_singleton_self _
    · set k := S.min' hS with hkdef
      have hkS : k ∈ S := S.min'_mem hS
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (ih (S.erase k) (Finset.erase_ssubset hkS))
      have hset : ((S.erase k) ∆ T) ∆ {k} = S ∆ T := by
        ext a
        simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
        by_cases hak : a = k <;> by_cases haS : a ∈ S <;> by_cases haT : a ∈ T <;>
          simp_all
      have hg := basisGenerator_mul_mem_span_symmDiff B v hv k ((S.erase k) ∆ T)
      rw [hset] at hg
      rw [basisMonomial_eq_min_mul_erase B v hS, ← hkdef, mul_assoc, ← hc, mul_smul_comm]
      exact Submodule.smul_mem _ _ hg

end Monomial

section CliffBasis

variable {N : ℕ} (v : Module.Basis (Fin N) ℂ V)

open scoped symmDiff

omit [FiniteDimensional ℂ V] in


/-- The orthogonal-basis monomials span the entire Clifford algebra. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem span_range_basisMonomial_eq_top (hv : B.IsOrthoᵢ v) :
    Submodule.span ℂ (Set.range (basisMonomial B v)) = ⊤ := by
  set W := Submodule.span ℂ (Set.range (basisMonomial B v)) with hWdef
  have hmem : ∀ S, basisMonomial B v S ∈ W := fun S => Submodule.subset_span ⟨S, rfl⟩
  have h1 : (1 : BilinearCliffordAlgebra B) ∈ W := basisMonomial_empty B v ▸ hmem ∅
  have hbmul : ∀ S T, basisMonomial B v S * basisMonomial B v T ∈ W := fun S T =>
    Submodule.span_mono (by rintro _ rfl; exact ⟨S ∆ T, rfl⟩) (basisMonomial_mul_mem_span_symmDiff B v hv S T)
  have hWmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W := by
    have hle : W * W ≤ W := by
      rw [hWdef, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨S, rfl⟩, _, ⟨T, rfl⟩, rfl⟩
      exact hbmul S T
    exact fun x hx y hy => hle (Submodule.mul_mem_mul hx hy)
  rw [eq_top_iff]
  rintro x -
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [Algebra.algebraMap_eq_smul_one]; exact W.smul_mem r h1
  | ι w =>
      have hexp : CliffordAlgebra.ι (quadraticForm B) w = ∑ i, v.repr w i • basisGenerator B v i := by
        conv_lhs => rw [← v.sum_repr w]
        rw [map_sum]; simp only [map_smul, basisGenerator]
      rw [hexp]
      exact W.sum_mem (fun i _ => W.smul_mem _ (basisMonomial_singleton B v i ▸ hmem {i}))
  | mul a b ha hb => exact hWmul a ha b hb
  | add a b ha hb => exact W.add_mem ha hb

omit [FiniteDimensional ℂ V] in
include v in


/-- The Clifford algebra on a space with a finite basis of size N has complex dimension two to the power N. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem finrank_eq_two_pow : Module.finrank ℂ (BilinearCliffordAlgebra B) = 2 ^ N := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  rw [(CliffordAlgebra.equivExterior (quadraticForm B)).finrank_eq,
    Module.finrank_eq_card_basis (Module.Basis.ExteriorAlgebra v),
    Fintype.card_finset, Fintype.card_fin]


/-- The complex basis of a Clifford algebra indexed by finite subsets of an orthogonal basis. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
noncomputable def finsetMonomialBasis (hv : B.IsOrthoᵢ v) :
    Module.Basis (Finset (Fin N)) ℂ (BilinearCliffordAlgebra B) :=
  basisOfTopLeSpanOfCardEqFinrank (basisMonomial B v) (span_range_basisMonomial_eq_top B v hv).ge
    (by rw [Fintype.card_finset, Fintype.card_fin, finrank_eq_two_pow B v])

omit [FiniteDimensional ℂ V] in
/-- The finite-subset basis evaluates to the corresponding ordered Clifford monomial. -/
@[simp] theorem finsetMonomialBasis_apply (hv : B.IsOrthoᵢ v) (S : Finset (Fin N)) :
    finsetMonomialBasis B v hv S = basisMonomial B v S := by
  simp only [finsetMonomialBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

end CliffBasis

section TraceForm

variable {N : ℕ} (v : Module.Basis (Fin N) ℂ V)

open scoped symmDiff

omit [FiniteDimensional ℂ V] in

/-- Left multiplication by a scalar multiple is the corresponding scalar multiple of left multiplication. -/
theorem mulLeft_smul (c : ℂ) (z : BilinearCliffordAlgebra B) :
    LinearMap.mulLeft ℂ (c • z) = c • LinearMap.mulLeft ℂ z := by
  ext w; simp

omit [FiniteDimensional ℂ V] in


/-- The trace of left multiplication by a basis monomial is two to the basis size for the empty monomial and zero otherwise. -/
theorem trace_mulLeft_basisMonomial (hv : B.IsOrthoᵢ v) (R : Finset (Fin N)) :
    LinearMap.trace ℂ (BilinearCliffordAlgebra B) (LinearMap.mulLeft ℂ (basisMonomial B v R))
      = if R = ∅ then (2 ^ N : ℂ) else 0 := by
  classical
  have htr : Matrix.trace (LinearMap.toMatrix (finsetMonomialBasis B v hv) (finsetMonomialBasis B v hv)
      (LinearMap.mulLeft ℂ (basisMonomial B v R)))
      = ∑ T, (finsetMonomialBasis B v hv).repr (basisMonomial B v R * basisMonomial B v T) T := by
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply,
      finsetMonomialBasis_apply]
  rw [LinearMap.trace_eq_matrix_trace ℂ (finsetMonomialBasis B v hv), htr]
  by_cases hR : R = ∅
  · subst hR
    rw [if_pos rfl]
    have hone : ∀ T : Finset (Fin N),
        (finsetMonomialBasis B v hv).repr (basisMonomial B v ∅ * basisMonomial B v T) T = 1 := by
      intro T
      rw [basisMonomial_empty, one_mul, ← finsetMonomialBasis_apply B v hv T, Module.Basis.repr_self_apply, if_pos rfl]
    rw [Finset.sum_congr rfl (fun T _ => hone T), Finset.sum_const, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [if_neg hR]
    refine Finset.sum_eq_zero (fun T _ => ?_)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (basisMonomial_mul_mem_span_symmDiff B v hv R T)
    rw [← hc, ← finsetMonomialBasis_apply B v hv (R ∆ T), map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, if_neg, smul_zero]
    intro h
    exact hR (by rw [← Finset.bot_eq_empty]; exact symmDiff_eq_right.mp h)

omit [FiniteDimensional ℂ V] in


/-- The trace of left multiplication by the product of two distinct orthogonal-basis monomials is zero. -/
theorem trace_mulLeft_basisMonomial_mul_eq_zero_of_ne (hv : B.IsOrthoᵢ v) {S T : Finset (Fin N)} (hST : S ≠ T) :
    LinearMap.trace ℂ (BilinearCliffordAlgebra B) (LinearMap.mulLeft ℂ (basisMonomial B v S * basisMonomial B v T)) = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (basisMonomial_mul_mem_span_symmDiff B v hv S T)
  rw [← hc, mulLeft_smul, map_smul, trace_mulLeft_basisMonomial B v hv, if_neg, smul_zero]
  intro h
  exact hST (symmDiff_eq_bot.mp (Finset.bot_eq_empty ▸ h))

omit [FiniteDimensional ℂ V] in


/-- For a nondegenerate orthogonal basis, the trace of left multiplication by the square of any basis monomial is nonzero. -/
theorem trace_mulLeft_basisMonomial_sq_ne_zero (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate)
    (T : Finset (Fin N)) :
    LinearMap.trace ℂ (BilinearCliffordAlgebra B) (LinearMap.mulLeft ℂ (basisMonomial B v T * basisMonomial B v T)) ≠ 0 := by
  haveI : Nontrivial (BilinearCliffordAlgebra B) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_eq_two_pow B v]; exact pow_pos (by norm_num) N)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (basisMonomial_mul_mem_span_symmDiff B v hv T T)
  have hunit : IsUnit (basisMonomial B v T * basisMonomial B v T) :=
    (isUnit_basisMonomial B v hv hnd T).mul (isUnit_basisMonomial B v hv hnd T)
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hunit.ne_zero hc.symm
  have hTT : T ∆ T = (∅ : Finset (Fin N)) := by rw [symmDiff_self, Finset.bot_eq_empty]
  rw [← hc, mulLeft_smul, map_smul, trace_mulLeft_basisMonomial B v hv, if_pos hTT, smul_eq_mul]
  exact mul_ne_zero hcne (pow_ne_zero N two_ne_zero)

end TraceForm


/-- The Clifford algebra of a symmetric nondegenerate bilinear form on a finite-dimensional complex space is semisimple. -/
@[source_ref "Chapter3/Problem3.9.5" (role := primary)]
theorem isSemisimpleRing_of_nondegenerate
    (hsymm : ∀ x y, B x y = B y x) (hnd : B.Nondegenerate) :
    IsSemisimpleRing (BilinearCliffordAlgebra B) := by
  classical
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero

  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp ⟨hsymm⟩)
  apply isSemisimpleRing_of_trace_mulLeft_nondegenerate

  intro x hx

  let τ : BilinearCliffordAlgebra B →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ (BilinearCliffordAlgebra B)).comp (Algebra.lmul ℂ (BilinearCliffordAlgebra B)).toLinearMap
  have hτ : ∀ z, τ z = LinearMap.trace ℂ (BilinearCliffordAlgebra B) (LinearMap.mulLeft ℂ z) := fun _ => rfl

  have hcoord : ∀ T, (finsetMonomialBasis B v hv).repr x T = 0 := by
    intro T
    have hexp : x = ∑ S, (finsetMonomialBasis B v hv).repr x S • basisMonomial B v S := by
      conv_lhs => rw [← (finsetMonomialBasis B v hv).sum_repr x]
      simp only [finsetMonomialBasis_apply]
    have hsum : τ (x * basisMonomial B v T)
        = (finsetMonomialBasis B v hv).repr x T • τ (basisMonomial B v T * basisMonomial B v T) := by
      conv_lhs => rw [hexp, Finset.sum_mul, map_sum]
      rw [Finset.sum_eq_single T]
      · rw [smul_mul_assoc, map_smul]
      · intro S _ hST
        rw [smul_mul_assoc, map_smul, hτ, trace_mulLeft_basisMonomial_mul_eq_zero_of_ne B v hv hST, smul_zero]
      · intro hT; exact absurd (Finset.mem_univ T) hT
    have hzero : (finsetMonomialBasis B v hv).repr x T • τ (basisMonomial B v T * basisMonomial B v T) = 0 := by
      rw [← hsum, hτ]; exact hx (basisMonomial B v T)
    have hne : τ (basisMonomial B v T * basisMonomial B v T) ≠ 0 := by
      rw [hτ]; exact trace_mulLeft_basisMonomial_sq_ne_zero B v hv hnd T
    exact (smul_eq_zero.mp hzero).resolve_right hne

  apply (finsetMonomialBasis B v hv).repr.injective
  rw [map_zero]
  ext T
  rw [hcoord T, Finsupp.zero_apply]


section CenterEven

variable {N : ℕ} (v : Module.Basis (Fin N) ℂ V)

open scoped symmDiff

omit [FiniteDimensional ℂ V] in


/-- An auxiliary multiplication statement involving an orthogonal-basis generator and a basis monomial. -/
theorem auxiliary_fact1 (hv : B.IsOrthoᵢ v) {i : Fin N} :
    ∀ T : Finset (Fin N), i ∉ T →
      basisGenerator B v i * basisMonomial B v T = (-1 : ℂ) ^ T.card • (basisMonomial B v T * basisGenerator B v i) := by
  intro T
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    intro hiT
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp
    · have hkT : T.min' hT ∈ T := T.min'_mem hT
      set k := T.min' hT with hk
      have hik : i ≠ k := fun h => hiT (h ▸ hkT)
      have hiT' : i ∉ T.erase k := fun h => hiT (Finset.mem_of_mem_erase h)
      have hcard : T.card = (T.erase k).card + 1 := by
        rw [Finset.card_erase_of_mem hkT, Nat.sub_add_cancel (Finset.card_pos.mpr hT)]
      have hpeel : basisMonomial B v T = basisGenerator B v k * basisMonomial B v (T.erase k) := by
        rw [basisMonomial_eq_min_mul_erase B v hT, ← hk]
      calc basisGenerator B v i * basisMonomial B v T
          = basisGenerator B v i * (basisGenerator B v k * basisMonomial B v (T.erase k)) := by rw [hpeel]
        _ = (basisGenerator B v i * basisGenerator B v k) * basisMonomial B v (T.erase k) := by rw [mul_assoc]
        _ = (-(basisGenerator B v k * basisGenerator B v i)) * basisMonomial B v (T.erase k) := by rw [basisGenerator_mul_eq_neg_mul B v hv hik]
        _ = -(basisGenerator B v k * (basisGenerator B v i * basisMonomial B v (T.erase k))) := by rw [neg_mul, mul_assoc]
        _ = -(basisGenerator B v k * ((-1 : ℂ) ^ (T.erase k).card • (basisMonomial B v (T.erase k) * basisGenerator B v i))) := by
              rw [ih (T.erase k) (Finset.erase_ssubset hkT) hiT']
        _ = (-1 : ℂ) ^ T.card • (basisGenerator B v k * (basisMonomial B v (T.erase k) * basisGenerator B v i)) := by
              rw [mul_smul_comm, ← neg_smul, hcard, pow_succ, mul_neg_one]
        _ = (-1 : ℂ) ^ T.card • (basisMonomial B v T * basisGenerator B v i) := by rw [hpeel, mul_assoc]

omit [FiniteDimensional ℂ V] in


/-- A second auxiliary multiplication statement involving an orthogonal-basis generator and a basis monomial. -/
theorem auxiliary_fact2 (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (i : Fin N) (S : Finset (Fin N)) :
    basisGenerator B v i * basisMonomial B v S = (-1 : ℂ) ^ (S.erase i).card • (basisMonomial B v S * basisGenerator B v i) := by
  by_cases hiS : i ∈ S
  ·
    set T := S.erase i with hT
    have hiT : i ∉ T := Finset.notMem_erase i S
    have hset : T ∆ ({i} : Finset (Fin N)) = S := by
      ext a
      simp only [hT, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      by_cases hai : a = i <;> simp [hai, hiS]
    obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp (basisGenerator_mul_mem_span_symmDiff B v hv i T)
    rw [hset] at hδ

    haveI : Nontrivial (BilinearCliffordAlgebra B) :=
      Module.nontrivial_of_finrank_pos (by rw [finrank_eq_two_pow B v]; positivity)
    have hδne : δ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hδ
      exact ((isUnit_basisGenerator B v hv hnd i).mul (isUnit_basisMonomial B v hv hnd T)).ne_zero hδ.symm
    have hSeq : basisMonomial B v S = δ⁻¹ • (basisGenerator B v i * basisMonomial B v T) := by
      rw [← hδ, smul_smul, inv_mul_cancel₀ hδne, one_smul]

    set c : ℂ := (-1 : ℂ) ^ T.card with hc
    have hcc : c * c = 1 := by rw [hc, ← pow_add, ← two_mul, pow_mul]; simp
    have hcomm : basisMonomial B v T * basisGenerator B v i = c • (basisGenerator B v i * basisMonomial B v T) := by
      rw [auxiliary_fact1 B v hv T hiT, ← hc, smul_smul, hcc, one_smul]

    have hL : basisGenerator B v i * basisMonomial B v S = δ⁻¹ • (basisGenerator B v i * basisGenerator B v i * basisMonomial B v T) := by
      rw [hSeq, mul_smul_comm, ← mul_assoc]
    have hR : basisMonomial B v S * basisGenerator B v i = (δ⁻¹ * c) • (basisGenerator B v i * basisGenerator B v i * basisMonomial B v T) := by
      rw [hSeq, smul_mul_assoc, mul_assoc, hcomm, mul_smul_comm, ← mul_assoc, smul_smul]
    rw [hL, hR, smul_smul]
    congr 1
    rw [mul_left_comm, hcc, mul_one]
  ·
    rw [Finset.erase_eq_of_notMem hiS]
    exact auxiliary_fact1 B v hv S hiS

omit [FiniteDimensional ℂ V] in


/-- An element commuting with every generator from a basis commutes with every element of the Clifford algebra. -/
theorem commute_all_of_commute_basisGenerator {x : BilinearCliffordAlgebra B}
    (h : ∀ i : Fin N, x * basisGenerator B v i = basisGenerator B v i * x) (y : BilinearCliffordAlgebra B) :
    x * y = y * x := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => rw [Algebra.commutes]
  | ι w =>
      have hexp : CliffordAlgebra.ι (quadraticForm B) w = ∑ i, v.repr w i • basisGenerator B v i := by
        conv_lhs => rw [← v.sum_repr w]
        rw [map_sum]; simp only [map_smul, basisGenerator]
      rw [hexp, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by rw [mul_smul_comm, smul_mul_assoc, h i])
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]

omit [FiniteDimensional ℂ V] in


/-- For a nondegenerate bilinear form with an even orthogonal basis, the center of the associated Clifford algebra is contained in the scalar subalgebra. -/
theorem center_le_bot_of_even (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (hN : Even N) :
    Subalgebra.center ℂ (BilinearCliffordAlgebra B) ≤ ⊥ := by
  intro x hx
  have hcomm : ∀ i, basisGenerator B v i * x = x * basisGenerator B v i := fun i =>
    Subalgebra.mem_center_iff.mp hx (basisGenerator B v i)
  set c := (finsetMonomialBasis B v hv).repr x with hcdef
  have hxexp : x = ∑ S, c S • basisMonomial B v S := by
    conv_lhs => rw [← (finsetMonomialBasis B v hv).sum_repr x]
    simp only [finsetMonomialBasis_apply, hcdef]

  have key : ∀ i : Fin N, ∀ S : Finset (Fin N),
      c S * ((-1 : ℂ) ^ (S.erase i).card - 1) = 0 := by
    intro i
    have hexpand : (∑ S, (c S * (-1 : ℂ) ^ (S.erase i).card) • (basisMonomial B v S * basisGenerator B v i))
        = ∑ S, c S • (basisMonomial B v S * basisGenerator B v i) := by
      have e1 : basisGenerator B v i * x
          = ∑ S, (c S * (-1 : ℂ) ^ (S.erase i).card) • (basisMonomial B v S * basisGenerator B v i) := by
        rw [hxexp, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun S _ => by
          rw [mul_smul_comm, auxiliary_fact2 B v hv hnd i S, smul_smul])
      have e2 : x * basisGenerator B v i = ∑ S, c S • (basisMonomial B v S * basisGenerator B v i) := by
        rw [hxexp, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun S _ => by rw [smul_mul_assoc])
      rw [← e1, ← e2, hcomm i]
    have hsum0 : (∑ S, (c S * ((-1 : ℂ) ^ (S.erase i).card - 1)) • (basisMonomial B v S * basisGenerator B v i)) = 0 := by
      rw [← sub_eq_zero.mpr hexpand, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun S _ => by rw [mul_sub, mul_one, sub_smul])

    set w : BilinearCliffordAlgebra B := (B (v i) (v i))⁻¹ • basisGenerator B v i with hwdef
    have hw : basisGenerator B v i * w = 1 := by
      rw [hwdef, mul_smul_comm, basisGenerator_sq, Algebra.smul_def, ← map_mul,
        inv_mul_cancel₀ (bilin_self_ne_zero_of_orthogonal_nondegenerate B v hv hnd i), map_one]
    have happly := congrArg (LinearMap.mulRight ℂ w) hsum0
    rw [map_zero, map_sum] at happly
    simp only [map_smul, LinearMap.mulRight_apply, mul_assoc, hw, mul_one] at happly

    have hli := (finsetMonomialBasis B v hv).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    exact hli (fun S => c S * ((-1 : ℂ) ^ (S.erase i).card - 1))
      (by simpa only [finsetMonomialBasis_apply] using happly)

  have hcS : ∀ S : Finset (Fin N), S ≠ ∅ → c S = 0 := by
    intro S hS
    obtain ⟨i, hodd⟩ : ∃ i, Odd (S.erase i).card := by
      rcases Nat.even_or_odd S.card with hpar | hpar
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        refine ⟨i, ?_⟩
        rw [Finset.card_erase_of_mem hi]
        obtain ⟨k, hk⟩ := hpar
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
        exact ⟨k - 1, by omega⟩
      · have hne_univ : S ≠ Finset.univ := by
          intro h
          rw [h, Finset.card_univ, Fintype.card_fin] at hpar
          exact (Nat.not_odd_iff_even.mpr hN) hpar
        obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
          by_contra hcon
          exact hne_univ (Finset.eq_univ_iff_forall.mpr (by simpa using hcon))
        exact ⟨i, by rw [Finset.erase_eq_of_notMem hi]; exact hpar⟩
    have hval : (-1 : ℂ) ^ (S.erase i).card - 1 = -2 := by rw [hodd.neg_one_pow]; ring
    have hk := key i S
    rw [hval] at hk
    exact (mul_eq_zero.mp hk).resolve_right (by norm_num)

  have hxval : x = c ∅ • (1 : BilinearCliffordAlgebra B) := by
    rw [hxexp, Finset.sum_eq_single (∅ : Finset (Fin N))]
    · rw [basisMonomial_empty]
    · exact fun S _ hS => by rw [hcS S hS, zero_smul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [Algebra.mem_bot]
  exact ⟨c ∅, by rw [Algebra.algebraMap_eq_smul_one]; exact hxval.symm⟩

end CenterEven

section CenterOdd

variable {N : ℕ} (v : Module.Basis (Fin N) ℂ V)

open scoped symmDiff

omit [FiniteDimensional ℂ V] in


/-- For an odd-dimensional nondegenerate orthogonal basis, the full basis monomial belongs to the center. -/
theorem basisMonomial_univ_mem_center_of_odd (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (hN : Odd N) :
    basisMonomial B v Finset.univ ∈ Subalgebra.center ℂ (BilinearCliffordAlgebra B) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  refine (commute_all_of_commute_basisGenerator B v (fun i => ?_) y).symm

  have hcard : (Finset.univ.erase i).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have heven : Even (Finset.univ.erase i).card := by
    rw [hcard]; rcases hN with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have hgc := auxiliary_fact2 B v hv hnd i Finset.univ
  rw [heven.neg_one_pow, one_smul] at hgc
  exact hgc.symm

omit [FiniteDimensional ℂ V] in


/-- The center of the Clifford algebra lies in the span of the empty and full orthogonal-basis monomials. -/
theorem center_le_span_one_volume (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) :
    (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule ≤
      Submodule.span ℂ {basisMonomial B v ∅, basisMonomial B v Finset.univ} := by
  intro x hx
  have hxc : x ∈ Subalgebra.center ℂ (BilinearCliffordAlgebra B) := hx
  have hcomm : ∀ i, basisGenerator B v i * x = x * basisGenerator B v i := fun i =>
    Subalgebra.mem_center_iff.mp hxc (basisGenerator B v i)
  set c := (finsetMonomialBasis B v hv).repr x with hcdef
  have hxexp : x = ∑ S, c S • basisMonomial B v S := by
    conv_lhs => rw [← (finsetMonomialBasis B v hv).sum_repr x]
    simp only [finsetMonomialBasis_apply, hcdef]

  have key : ∀ i : Fin N, ∀ S : Finset (Fin N),
      c S * ((-1 : ℂ) ^ (S.erase i).card - 1) = 0 := by
    intro i
    have hexpand : (∑ S, (c S * (-1 : ℂ) ^ (S.erase i).card) • (basisMonomial B v S * basisGenerator B v i))
        = ∑ S, c S • (basisMonomial B v S * basisGenerator B v i) := by
      have e1 : basisGenerator B v i * x
          = ∑ S, (c S * (-1 : ℂ) ^ (S.erase i).card) • (basisMonomial B v S * basisGenerator B v i) := by
        rw [hxexp, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun S _ => by
          rw [mul_smul_comm, auxiliary_fact2 B v hv hnd i S, smul_smul])
      have e2 : x * basisGenerator B v i = ∑ S, c S • (basisMonomial B v S * basisGenerator B v i) := by
        rw [hxexp, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun S _ => by rw [smul_mul_assoc])
      rw [← e1, ← e2, hcomm i]
    have hsum0 : (∑ S, (c S * ((-1 : ℂ) ^ (S.erase i).card - 1)) • (basisMonomial B v S * basisGenerator B v i)) = 0 := by
      rw [← sub_eq_zero.mpr hexpand, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun S _ => by rw [mul_sub, mul_one, sub_smul])
    set w : BilinearCliffordAlgebra B := (B (v i) (v i))⁻¹ • basisGenerator B v i with hwdef
    have hw : basisGenerator B v i * w = 1 := by
      rw [hwdef, mul_smul_comm, basisGenerator_sq, Algebra.smul_def, ← map_mul,
        inv_mul_cancel₀ (bilin_self_ne_zero_of_orthogonal_nondegenerate B v hv hnd i), map_one]
    have happly := congrArg (LinearMap.mulRight ℂ w) hsum0
    rw [map_zero, map_sum] at happly
    simp only [map_smul, LinearMap.mulRight_apply, mul_assoc, hw, mul_one] at happly
    have hli := (finsetMonomialBasis B v hv).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    exact hli (fun S => c S * ((-1 : ℂ) ^ (S.erase i).card - 1))
      (by simpa only [finsetMonomialBasis_apply] using happly)

  have hcS : ∀ S : Finset (Fin N), S ≠ ∅ → S ≠ Finset.univ → c S = 0 := by
    intro S hS hSu
    obtain ⟨i, hodd⟩ : ∃ i, Odd (S.erase i).card := by
      rcases Nat.even_or_odd S.card with hpar | hpar
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        refine ⟨i, ?_⟩
        rw [Finset.card_erase_of_mem hi]
        obtain ⟨k, hk⟩ := hpar
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
        exact ⟨k - 1, by omega⟩
      · obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
          by_contra hcon
          exact hSu (Finset.eq_univ_iff_forall.mpr (by simpa using hcon))
        exact ⟨i, by rw [Finset.erase_eq_of_notMem hi]; exact hpar⟩
    have hval : (-1 : ℂ) ^ (S.erase i).card - 1 = -2 := by rw [hodd.neg_one_pow]; ring
    have hk := key i S
    rw [hval] at hk
    exact (mul_eq_zero.mp hk).resolve_right (by norm_num)

  rw [hxexp]
  refine Submodule.sum_mem _ (fun S _ => ?_)
  by_cases hS : S = ∅
  · exact hS ▸ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  by_cases hSu : S = Finset.univ
  · exact hSu ▸ Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  · rw [hcS S hS hSu, zero_smul]; exact Submodule.zero_mem _

omit [FiniteDimensional ℂ V] in


/-- For an odd-dimensional nondegenerate orthogonal basis, the center of the Clifford algebra has complex dimension two. -/
theorem center_finrank_eq_two_of_odd (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) (hN : Odd N) :
    Module.finrank ℂ (Subalgebra.center ℂ (BilinearCliffordAlgebra B)) = 2 := by
  have hne : (∅ : Finset (Fin N)) ≠ Finset.univ := by
    intro h
    have hc : (Finset.univ : Finset (Fin N)).card = 0 := by rw [← h]; rfl
    rw [Finset.card_univ, Fintype.card_fin] at hc
    rcases hN with ⟨k, hk⟩; omega
  set idx : Fin 2 → Finset (Fin N) := ![∅, Finset.univ] with hidx
  have hidxinj : Function.Injective idx := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  set w : Fin 2 → BilinearCliffordAlgebra B := fun i => basisMonomial B v (idx i) with hwdef
  have hwli : LinearIndependent ℂ w := by
    have hb := ((finsetMonomialBasis B v hv).linearIndependent).comp idx hidxinj
    have hfun : w = ⇑(finsetMonomialBasis B v hv) ∘ idx := by
      funext i; simp [hwdef, finsetMonomialBasis_apply]
    rw [hfun]; exact hb
  have hrange : Set.range w = {basisMonomial B v ∅, basisMonomial B v Finset.univ} := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp [hwdef, hidx]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [hwdef, hidx]⟩
      · exact ⟨1, by simp [hwdef, hidx]⟩

  have hspan : Submodule.span ℂ (Set.range w) = (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule := by
    apply le_antisymm
    · rw [hrange, Submodule.span_le]
      rintro z (rfl | rfl)
      · rw [basisMonomial_empty]; exact Subalgebra.one_mem _
      · exact basisMonomial_univ_mem_center_of_odd B v hv hnd hN
    · rw [hrange]; exact center_le_span_one_volume B v hv hnd
  have hcard : Module.finrank ℂ (Submodule.span ℂ (Set.range w)) = 2 := by
    rw [finrank_span_eq_card hwli, Fintype.card_fin]
  rw [← Subalgebra.finrank_toSubmodule, ← hspan, hcard]

end CenterOdd

section GradeInvolution

variable {N : ℕ} (v : Module.Basis (Fin N) ℂ V)

open scoped symmDiff

omit [FiniteDimensional ℂ V] in


/-- An auxiliary statement about an orthogonal-basis monomial in a Clifford algebra. -/
theorem auxiliary_fact3 (S : Finset (Fin N)) :
    CliffordAlgebra.involute (basisMonomial B v S) = (-1 : ℂ) ^ S.card • basisMonomial B v S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · set k := S.min' hS with hkdef
      have hkS : k ∈ S := S.min'_mem hS
      have hpeel : basisMonomial B v S = basisGenerator B v k * basisMonomial B v (S.erase k) := by rw [basisMonomial_eq_min_mul_erase B v hS, ← hkdef]
      have hcard : S.card = (S.erase k).card + 1 := by
        rw [Finset.card_erase_of_mem hkS, Nat.sub_add_cancel (Finset.card_pos.mpr hS)]
      have hgk : CliffordAlgebra.involute (basisGenerator B v k) = - basisGenerator B v k := by
        rw [basisGenerator]; exact CliffordAlgebra.involute_ι _
      rw [hpeel, map_mul, hgk, ih (S.erase k) (Finset.erase_ssubset hkS),
        neg_mul, mul_smul_comm, ← neg_smul, ← hpeel, hcard, pow_succ]
      congr 1
      ring

omit [FiniteDimensional ℂ V] in


/-- The square of the full monomial of a nondegenerate orthogonal basis is a nonzero scalar multiple of one. -/
theorem exists_basisMonomial_univ_sq_eq_smul_one (hv : B.IsOrthoᵢ v) (hnd : B.Nondegenerate) :
    ∃ μ : ℂ, μ ≠ 0 ∧ basisMonomial B v Finset.univ * basisMonomial B v Finset.univ = μ • (1 : BilinearCliffordAlgebra B) := by
  have hmem := basisMonomial_mul_mem_span_symmDiff B v hv Finset.univ Finset.univ
  have hset : (Finset.univ : Finset (Fin N)) ∆ Finset.univ = ∅ := by
    ext a; simp
  rw [hset, basisMonomial_empty] at hmem
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨μ, ?_, hμ.symm⟩
  intro hμ0
  haveI : Nontrivial (BilinearCliffordAlgebra B) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_eq_two_pow B v]; positivity)
  have hunit : IsUnit (basisMonomial B v Finset.univ * basisMonomial B v Finset.univ) :=
    (isUnit_basisMonomial B v hv hnd Finset.univ).mul (isUnit_basisMonomial B v hv hnd Finset.univ)
  rw [← hμ, hμ0, zero_smul] at hunit
  exact (not_isUnit_zero) hunit

end GradeInvolution

set_option maxHeartbeats 400000 in


/-- For a symmetric nondegenerate form of dimension twice a natural number, the Clifford algebra is algebra-equivalent to the endomorphism algebra of a space of dimension the corresponding power of two. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem exists_algEquiv_end_of_finrank_even
    (hsymm : ∀ x y, B x y = B y x) (hnd : B.Nondegenerate)
    (n : ℕ) (hdim : Module.finrank ℂ V = 2 * n) :
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S),
      Module.finrank ℂ S = 2 ^ n ∧ Nonempty (BilinearCliffordAlgebra B ≃ₐ[ℂ] Module.End ℂ S) := by
  classical
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero

  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp ⟨hsymm⟩)
  have hNeven : Even (Module.finrank ℂ V) := ⟨n, by rw [hdim]; ring⟩

  haveI hss : IsSemisimpleRing (BilinearCliffordAlgebra B) := isSemisimpleRing_of_nondegenerate B hsymm hnd
  have hcent : Subalgebra.center ℂ (BilinearCliffordAlgebra B) = ⊥ :=
    le_antisymm (center_le_bot_of_even B v hv hnd hNeven) bot_le
  have hcf : Module.finrank ℂ (Subalgebra.center ℂ (BilinearCliffordAlgebra B)) = 1 := by
    rw [hcent]; exact Subalgebra.finrank_bot
  haveI : Nontrivial (BilinearCliffordAlgebra B) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_eq_two_pow B v]; positivity)

  obtain ⟨m, d, hd, ⟨eiso⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (BilinearCliffordAlgebra B)
  haveI hmatnt : ∀ i : Fin m, Nontrivial (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
    intro i
    haveI := hd i
    haveI : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    infer_instance

  set P := (Π i : Fin m, Matrix (Fin (d i)) (Fin (d i)) ℂ) with hPdef
  have hsingle_cent : ∀ i : Fin m,
      (Pi.single i 1 : P) ∈ Subalgebra.center ℂ P := by
    intro i
    rw [Subalgebra.mem_center_iff]
    intro b
    funext j
    simp only [Pi.mul_apply]
    rcases eq_or_ne j i with rfl | hji
    · rw [Pi.single_eq_same, mul_one, one_mul]
    · rw [Pi.single_eq_of_ne hji, mul_zero, zero_mul]
  let g : Fin m → BilinearCliffordAlgebra B := fun i => eiso.symm (Pi.single i 1)
  have hg_cent : ∀ i, g i ∈ Subalgebra.center ℂ (BilinearCliffordAlgebra B) := by
    intro i
    rw [Subalgebra.mem_center_iff]
    intro y
    have hs := Subalgebra.mem_center_iff.mp (hsingle_cent i) (eiso y)
    calc y * g i = eiso.symm (eiso y) * eiso.symm (Pi.single i 1) := by
            rw [AlgEquiv.symm_apply_apply]
      _ = eiso.symm (eiso y * Pi.single i 1) := by rw [← map_mul]
      _ = eiso.symm (Pi.single i 1 * eiso y) := by rw [hs]
      _ = eiso.symm (Pi.single i 1) * eiso.symm (eiso y) := by rw [map_mul]
      _ = g i * y := by rw [AlgEquiv.symm_apply_apply]
  have hbase : LinearIndependent ℂ (fun i : Fin m => (Pi.single i 1 : P)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have hj := congrFun ha j
    rw [Finset.sum_apply, Pi.zero_apply, Finset.sum_eq_single j] at hj
    · rw [Pi.smul_apply, Pi.single_eq_same] at hj
      exact (smul_eq_zero.mp hj).resolve_right one_ne_zero
    · intro b _ hbj
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hbj), smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hg_li : LinearIndependent ℂ g :=
    hbase.map' eiso.symm.toLinearMap (LinearMap.ker_eq_bot.mpr eiso.symm.injective)

  have hspan_le : Submodule.span ℂ (Set.range g) ≤
      (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hg_cent i
  have hmle : m ≤ 1 := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range g)) = m := by
      rw [finrank_span_eq_card hg_li, Fintype.card_fin]
    calc m = Module.finrank ℂ (Submodule.span ℂ (Set.range g)) := h1.symm
      _ ≤ Module.finrank ℂ (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule :=
          Submodule.finrank_mono hspan_le
      _ = 1 := hcf

  have hm : m = 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      subst h0
      haveI : Subsingleton P := by rw [hPdef]; infer_instance
      haveI : Subsingleton (BilinearCliffordAlgebra B) := eiso.injective.subsingleton
      exact false_of_nontrivial_of_subsingleton (BilinearCliffordAlgebra B)
    · omega
  subst hm

  set k := d default with hkdef
  let piU : P ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique fun i : Fin 1 =>
      Matrix (Fin (d i)) (Fin (d i)) ℂ) (fun r => rfl)
  let mEnd : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin k → ℂ) :=
    LinearMap.toMatrixAlgEquiv'.symm
  refine ⟨Fin k → ℂ, inferInstance, inferInstance, ?_,
    ⟨eiso.trans (piU.trans mEnd)⟩⟩

  have hfr_iso : Module.finrank ℂ (BilinearCliffordAlgebra B) = Module.finrank ℂ (Module.End ℂ (Fin k → ℂ)) :=
    (eiso.trans (piU.trans mEnd)).toLinearEquiv.finrank_eq
  have hfrS : Module.finrank ℂ (Fin k → ℂ) = k := by simp
  have hsq : k ^ 2 = (2 ^ n) ^ 2 := by
    have h1 : Module.finrank ℂ (Module.End ℂ (Fin k → ℂ)) = k ^ 2 := by
      rw [Module.finrank_linearMap, hfrS, sq]
    have h2 : Module.finrank ℂ (BilinearCliffordAlgebra B) = (2 ^ n) ^ 2 := by
      rw [finrank_eq_two_pow B v, hdim, ← pow_mul, mul_comm]
    rw [← h1, ← hfr_iso, h2]
  have hk : k = 2 ^ n := Nat.pow_left_injective (by norm_num) hsq
  rw [hfrS, hk]

set_option maxHeartbeats 400000 in


/-- For a symmetric nondegenerate form of odd dimension, the Clifford algebra is algebra-equivalent to a product of two nonzero square matrix algebras. -/
theorem exists_algEquiv_pi_matrix_of_finrank_odd
    (hsymm : ∀ x y, B x y = B y x) (hnd : B.Nondegenerate)
    (n : ℕ) (hdim : Module.finrank ℂ V = 2 * n + 1) :
    ∃ (d : Fin 2 → ℕ), (∀ i, 0 < d i) ∧
      Nonempty (BilinearCliffordAlgebra B ≃ₐ[ℂ] (Π i : Fin 2, Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
  classical
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp ⟨hsymm⟩)
  have hNodd : Odd (Module.finrank ℂ V) := ⟨n, by rw [hdim]⟩
  haveI hss : IsSemisimpleRing (BilinearCliffordAlgebra B) := isSemisimpleRing_of_nondegenerate B hsymm hnd
  haveI : Nontrivial (BilinearCliffordAlgebra B) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_eq_two_pow B v]; positivity)

  obtain ⟨m, d, hd, ⟨eiso⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (BilinearCliffordAlgebra B)
  set P := (Π i : Fin m, Matrix (Fin (d i)) (Fin (d i)) ℂ) with hPdef

  have hsingle_cent : ∀ i : Fin m, (Pi.single i 1 : P) ∈ Subalgebra.center ℂ P := by
    intro i
    rw [Subalgebra.mem_center_iff]
    intro b
    funext j
    simp only [Pi.mul_apply]
    rcases eq_or_ne j i with rfl | hji
    · rw [Pi.single_eq_same, mul_one, one_mul]
    · rw [Pi.single_eq_of_ne hji, mul_zero, zero_mul]
  let g : Fin m → BilinearCliffordAlgebra B := fun i => eiso.symm (Pi.single i 1)
  have hg_cent : ∀ i, g i ∈ Subalgebra.center ℂ (BilinearCliffordAlgebra B) := by
    intro i
    rw [Subalgebra.mem_center_iff]
    intro y
    have hs := Subalgebra.mem_center_iff.mp (hsingle_cent i) (eiso y)
    calc y * g i = eiso.symm (eiso y) * eiso.symm (Pi.single i 1) := by
            rw [AlgEquiv.symm_apply_apply]
      _ = eiso.symm (eiso y * Pi.single i 1) := by rw [← map_mul]
      _ = eiso.symm (Pi.single i 1 * eiso y) := by rw [hs]
      _ = eiso.symm (Pi.single i 1) * eiso.symm (eiso y) := by rw [map_mul]
      _ = g i * y := by rw [AlgEquiv.symm_apply_apply]
  have hbase : LinearIndependent ℂ (fun i : Fin m => (Pi.single i 1 : P)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have hj := congrFun ha j
    rw [Finset.sum_apply, Pi.zero_apply, Finset.sum_eq_single j] at hj
    · rw [Pi.smul_apply, Pi.single_eq_same] at hj
      exact (smul_eq_zero.mp hj).resolve_right one_ne_zero
    · intro b _ hbj
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hbj), smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hg_li : LinearIndependent ℂ g :=
    hbase.map' eiso.symm.toLinearMap (LinearMap.ker_eq_bot.mpr eiso.symm.injective)

  have hspan_le : Submodule.span ℂ (Set.range g) ≤
      (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hg_cent i


  have hg_span_center : (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule ≤
      Submodule.span ℂ (Set.range g) := by
    intro x hx
    have hxc : x ∈ Subalgebra.center ℂ (BilinearCliffordAlgebra B) := hx
    have hpc : eiso x ∈ Subalgebra.center ℂ P := by
      rw [Subalgebra.mem_center_iff]
      intro b
      have hs := Subalgebra.mem_center_iff.mp hxc (eiso.symm b)
      calc b * eiso x = eiso (eiso.symm b) * eiso x := by rw [AlgEquiv.apply_symm_apply]
        _ = eiso (eiso.symm b * x) := by rw [← map_mul]
        _ = eiso (x * eiso.symm b) := by rw [hs]
        _ = eiso x * eiso (eiso.symm b) := by rw [map_mul]
        _ = eiso x * b := by rw [AlgEquiv.apply_symm_apply]
    have hscalar : ∀ i : Fin m, ∃ c : ℂ, algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) c
        = (eiso x) i := by
      intro i
      have hpc' : eiso x ∈
          Subalgebra.center ℂ (Π j : Fin m, Matrix (Fin (d j)) (Fin (d j)) ℂ) := hpc
      rw [Subalgebra.center_pi] at hpc'
      have hcoord : (eiso x) i ∈ Subalgebra.center ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
        Subalgebra.mem_pi.mp hpc' i (Set.mem_univ i)
      have hbot : (eiso x) i ∈ (⊥ : Subalgebra ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) :=
        Algebra.IsCentral.out hcoord
      exact Algebra.mem_bot.mp hbot
    choose c hc using hscalar
    have hsum : eiso x = ∑ i, c i • (Pi.single i 1 : P) := by
      conv_lhs => rw [← Finset.univ_sum_single (eiso x)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← hc i, Algebra.algebraMap_eq_smul_one, Pi.single_smul]
    have hx_eq : x = ∑ i, c i • g i := by
      have h2 := congrArg eiso.symm hsum
      rw [AlgEquiv.symm_apply_apply, map_sum] at h2
      simp only [map_smul] at h2
      exact h2
    rw [hx_eq]
    exact Submodule.sum_mem _
      (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

  have hspan_eq : Submodule.span ℂ (Set.range g)
      = (Subalgebra.center ℂ (BilinearCliffordAlgebra B)).toSubmodule :=
    le_antisymm hspan_le hg_span_center
  have hcenter2 : Module.finrank ℂ (Submodule.span ℂ (Set.range g)) = 2 := by
    rw [hspan_eq]; exact center_finrank_eq_two_of_odd B v hv hnd hNodd
  have hm : m = 2 := by
    have hfs := finrank_span_eq_card hg_li
    rw [hcenter2, Fintype.card_fin] at hfs
    exact hfs.symm
  subst hm
  exact ⟨d, fun i => by haveI := hd i; exact Nat.pos_of_ne_zero (NeZero.ne _), ⟨eiso⟩⟩

set_option maxHeartbeats 1600000 in


/-- For a symmetric nondegenerate form of dimension twice a natural number plus one, the Clifford algebra is algebra-equivalent to a product of two endomorphism algebras on a space of dimension the corresponding power of two. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem exists_algEquiv_prod_end_of_finrank_odd
    (hsymm : ∀ x y, B x y = B y x) (hnd : B.Nondegenerate)
    (n : ℕ) (hdim : Module.finrank ℂ V = 2 * n + 1) :
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S),
      Module.finrank ℂ S = 2 ^ n ∧
      Nonempty (BilinearCliffordAlgebra B ≃ₐ[ℂ] (Module.End ℂ S × Module.End ℂ S)) := by
  classical
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero

  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp ⟨hsymm⟩)
  have hNodd : Odd (Module.finrank ℂ V) := ⟨n, by rw [hdim]⟩
  haveI : Nontrivial (BilinearCliffordAlgebra B) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_eq_two_pow B v]; positivity)

  obtain ⟨d, hdpos, ⟨eiso⟩⟩ := exists_algEquiv_pi_matrix_of_finrank_odd B hsymm hnd n hdim
  set P := (Π i : Fin 2, Matrix (Fin (d i)) (Fin (d i)) ℂ) with hPdef
  haveI hmatnt : ∀ i : Fin 2, Nontrivial (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
    intro i
    haveI : Nonempty (Fin (d i)) := ⟨⟨0, hdpos i⟩⟩
    infer_instance

  set e0 : P := Pi.single 0 1 with he0
  set e1 : P := Pi.single 1 1 with he1
  set g0 : BilinearCliffordAlgebra B := eiso.symm e0 with hg0
  set g1 : BilinearCliffordAlgebra B := eiso.symm e1 with hg1

  have he01 : e0 + e1 = 1 := by
    funext i; fin_cases i <;> simp +zetaDelta [Pi.add_apply]
  have he0e1 : e0 * e1 = 0 := by
    funext i; fin_cases i <;> simp +zetaDelta [Pi.mul_apply]
  have he0sq : e0 * e0 = e0 := by
    funext i; fin_cases i <;> simp +zetaDelta [Pi.mul_apply]
  have he0ne0 : e0 ≠ 0 := by
    intro h; have h0 := congrFun h 0; simp +zetaDelta at h0
  have he0ne1 : e0 ≠ 1 := by
    intro h; have h1 := congrFun h 1; simp +zetaDelta at h1
  have he0cent : e0 ∈ Subalgebra.center ℂ P := by
    rw [Subalgebra.mem_center_iff]
    intro b; funext j; fin_cases j <;> simp +zetaDelta [Pi.mul_apply]

  have hg01 : g0 + g1 = 1 := by rw [hg0, hg1, ← map_add, he01, map_one]
  have hg0g1 : g0 * g1 = 0 := by rw [hg0, hg1, ← map_mul, he0e1, map_zero]
  have hg0sq : g0 * g0 = g0 := by rw [hg0, ← map_mul, he0sq]
  have hg0ne0 : g0 ≠ 0 := by
    intro h; apply he0ne0; rw [← AlgEquiv.apply_symm_apply eiso e0, ← hg0, h, map_zero]
  have hg0ne1 : g0 ≠ 1 := by
    intro h; apply he0ne1; rw [← AlgEquiv.apply_symm_apply eiso e0, ← hg0, h, map_one]
  have hg0cent : g0 ∈ Subalgebra.center ℂ (BilinearCliffordAlgebra B) := by
    rw [Subalgebra.mem_center_iff]
    intro y
    have hs := Subalgebra.mem_center_iff.mp he0cent (eiso y)
    have h1 : g0 * y = eiso.symm (e0 * eiso y) := by
      rw [hg0, map_mul, AlgEquiv.symm_apply_apply]
    have h2 : y * g0 = eiso.symm (eiso y * e0) := by
      rw [hg0, map_mul, AlgEquiv.symm_apply_apply]
    rw [h1, h2, hs]

  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (center_le_span_one_volume B v hv hnd hg0cent)
  rw [basisMonomial_empty] at hab
  obtain ⟨μ, hμ0, hμ⟩ := exists_basisMonomial_univ_sq_eq_smul_one B v hv hnd

  have hne : (∅ : Finset (Fin (Module.finrank ℂ V))) ≠ Finset.univ := by
    intro h
    have hc : (Finset.univ : Finset (Fin (Module.finrank ℂ V))).card = 0 := by rw [← h]; simp
    rw [Finset.card_univ, Fintype.card_fin] at hc
    rw [hdim] at hc; omega
  have hidxinj : Function.Injective
      (![(∅ : Finset (Fin (Module.finrank ℂ V))), Finset.univ]) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hli : LinearIndependent ℂ ![(1 : BilinearCliffordAlgebra B), basisMonomial B v Finset.univ] := by
    have hcomp : ![(1 : BilinearCliffordAlgebra B), basisMonomial B v Finset.univ]
        = ⇑(finsetMonomialBasis B v hv) ∘ ![(∅ : Finset (Fin (Module.finrank ℂ V))), Finset.univ] := by
      funext i; fin_cases i <;> simp [finsetMonomialBasis_apply, basisMonomial_empty]
    rw [hcomp]
    exact (finsetMonomialBasis B v hv).linearIndependent.comp _ hidxinj

  have expand : (a • (1 : BilinearCliffordAlgebra B) + b • basisMonomial B v Finset.univ)
        * (a • (1 : BilinearCliffordAlgebra B) + b • basisMonomial B v Finset.univ)
      = (a * a + b * b * μ) • (1 : BilinearCliffordAlgebra B) + (2 * a * b) • basisMonomial B v Finset.univ := by
    rw [mul_add, add_mul, add_mul, smul_mul_smul_comm, smul_mul_smul_comm,
        smul_mul_smul_comm, smul_mul_smul_comm]
    simp only [mul_one, one_mul]
    rw [hμ]
    module
  have hidem : (a * a + b * b * μ - a) • (1 : BilinearCliffordAlgebra B)
      + (2 * a * b - b) • basisMonomial B v Finset.univ = 0 := by
    have h : (a • (1 : BilinearCliffordAlgebra B) + b • basisMonomial B v Finset.univ)
          * (a • (1 : BilinearCliffordAlgebra B) + b • basisMonomial B v Finset.univ)
        = a • (1 : BilinearCliffordAlgebra B) + b • basisMonomial B v Finset.univ := by rw [hab]; exact hg0sq
    rw [expand] at h
    rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]
    exact h
  have hzero : ∀ i, (![a * a + b * b * μ - a, 2 * a * b - b] : Fin 2 → ℂ) i = 0 := by
    apply (Fintype.linearIndependent_iff.mp hli)
    rw [Fin.sum_univ_two]
    simpa using hidem
  have heq2 : 2 * a * b - b = 0 := by simpa using hzero 1

  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, zero_smul, add_zero] at hab
    have hinj : Function.Injective (algebraMap ℂ (BilinearCliffordAlgebra B)) :=
      (algebraMap ℂ (BilinearCliffordAlgebra B)).injective
    have key : (a * a) • (1 : BilinearCliffordAlgebra B) = a • (1 : BilinearCliffordAlgebra B) := by
      have h := hg0sq
      rw [← hab, smul_mul_smul_comm, mul_one] at h
      exact h
    have haa : a * a = a := by
      have e2 := key
      rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at e2
      exact hinj e2
    have hfac : a * (a - 1) = 0 := by rw [mul_sub, mul_one, haa, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact hg0ne0 (by rw [← hab, h, zero_smul])
    · exact hg0ne1 (by rw [← hab, sub_eq_zero.mp h, one_smul])

  have h2a : 2 * a = 1 := by
    have hbf : b * (2 * a - 1) = 0 := by linear_combination heq2
    rcases mul_eq_zero.mp hbf with h | h
    · exact absurd h hb0
    · exact sub_eq_zero.mp h

  have hinv_u : CliffordAlgebra.involute (basisMonomial B v Finset.univ) = - basisMonomial B v Finset.univ := by
    rw [auxiliary_fact3]
    have hcard : (Finset.univ : Finset (Fin (Module.finrank ℂ V))).card = Module.finrank ℂ V := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard, hNodd.neg_one_pow, neg_one_smul]
  have hφg0 : CliffordAlgebra.involute g0 = g1 := by
    rw [← hab, map_add, map_smul, map_smul, map_one, hinv_u]
    have hlin : (a • (1 : BilinearCliffordAlgebra B) + b • (- basisMonomial B v Finset.univ))
          + (a • (1 : BilinearCliffordAlgebra B) + b • basisMonomial B v Finset.univ)
        = (2 * a) • (1 : BilinearCliffordAlgebra B) := by module
    have hone : (2 * a) • (1 : BilinearCliffordAlgebra B) = 1 := by rw [h2a, one_smul]
    have htgt : (a • (1 : BilinearCliffordAlgebra B) + b • (- basisMonomial B v Finset.univ)) + g0 = 1 := by
      rw [← hab, hlin, hone]
    have hcancel : (a • (1 : BilinearCliffordAlgebra B) + b • (- basisMonomial B v Finset.univ)) + g0 = g1 + g0 := by
      rw [htgt, add_comm g1 g0, hg01]
    exact add_right_cancel hcancel

  let φE : BilinearCliffordAlgebra B ≃ₐ[ℂ] BilinearCliffordAlgebra B := CliffordAlgebra.involuteEquiv
  have hφE : ∀ x, φE x = CliffordAlgebra.involute x := fun _ => rfl
  let ψ : P ≃ₐ[ℂ] P := (eiso.symm.trans φE).trans eiso
  have hψe0 : ψ e0 = e1 := by
    change eiso (φE (eiso.symm e0)) = e1
    rw [← hg0, hφE, hφg0, hg1, AlgEquiv.apply_symm_apply]

  set I0 : Submodule ℂ P := LinearMap.range (LinearMap.mulLeft ℂ e0) with hI0
  set I1 : Submodule ℂ P := LinearMap.range (LinearMap.mulLeft ℂ e1) with hI1
  have he0mul : ∀ p : P, e0 * p = Pi.single 0 (p 0) := by
    intro p; rw [he0]; funext j
    rcases eq_or_ne j 0 with rfl | hj
    · simp +zetaDelta [Pi.mul_apply, Pi.single_eq_same]
    · simp +zetaDelta [Pi.mul_apply, Pi.single_eq_of_ne hj]
  have he1mul : ∀ p : P, e1 * p = Pi.single 1 (p 1) := by
    intro p; rw [he1]; funext j
    rcases eq_or_ne j 1 with rfl | hj
    · simp +zetaDelta [Pi.mul_apply, Pi.single_eq_same]
    · simp +zetaDelta [Pi.mul_apply, Pi.single_eq_of_ne hj]
  have hI0eq : I0 = LinearMap.range
      (LinearMap.single ℂ (fun i : Fin 2 => Matrix (Fin (d i)) (Fin (d i)) ℂ) 0) := by
    rw [hI0]; apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [LinearMap.mulLeft_apply, he0mul]
      exact ⟨p 0, by rw [LinearMap.single_apply]⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨Pi.single 0 x, ?_⟩
      rw [LinearMap.mulLeft_apply, he0mul, LinearMap.single_apply]
      simp
  have hI1eq : I1 = LinearMap.range
      (LinearMap.single ℂ (fun i : Fin 2 => Matrix (Fin (d i)) (Fin (d i)) ℂ) 1) := by
    rw [hI1]; apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [LinearMap.mulLeft_apply, he1mul]
      exact ⟨p 1, by rw [LinearMap.single_apply]⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨Pi.single 1 x, ?_⟩
      rw [LinearMap.mulLeft_apply, he1mul, LinearMap.single_apply]
      simp
  have hfrI0 : Module.finrank ℂ I0 = d 0 * d 0 := by
    rw [hI0eq, LinearMap.finrank_range_of_inj
        (LinearMap.ker_eq_bot.mp (LinearMap.ker_single
          (R := ℂ) (φ := fun i : Fin 2 => Matrix (Fin (d i)) (Fin (d i)) ℂ) 0)),
      Module.finrank_matrix]
    simp
  have hfrI1 : Module.finrank ℂ I1 = d 1 * d 1 := by
    rw [hI1eq, LinearMap.finrank_range_of_inj
        (LinearMap.ker_eq_bot.mp (LinearMap.ker_single
          (R := ℂ) (φ := fun i : Fin 2 => Matrix (Fin (d i)) (Fin (d i)) ℂ) 1)),
      Module.finrank_matrix]
    simp
  have hψsymm_e1 : ψ.symm e1 = e0 := ψ.symm_apply_eq.mpr hψe0.symm
  have hmap : Submodule.map (ψ.toLinearEquiv : P →ₗ[ℂ] P) I0 = I1 := by
    rw [hI0, hI1]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe,
      AlgEquiv.coe_toLinearEquiv, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨x, ⟨q, rfl⟩, rfl⟩
      exact ⟨ψ q, by rw [map_mul, hψe0]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨ψ.symm (e1 * r), ⟨ψ.symm r, by rw [← hψsymm_e1, ← map_mul]⟩,
        ψ.apply_symm_apply _⟩
  have hfr_eq : d 1 * d 1 = d 0 * d 0 := by
    have hfm := LinearEquiv.finrank_map_eq ψ.toLinearEquiv I0
    rw [hmap] at hfm
    rw [← hfrI1, ← hfrI0, hfm]

  have hd01 : d 0 = d 1 := (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hfr_eq.symm
  have hfrP : Module.finrank ℂ P = d 0 * d 0 + d 1 * d 1 := by
    change Module.finrank ℂ (∀ i : Fin 2, Matrix (Fin (d i)) (Fin (d i)) ℂ) = _
    rw [Module.finrank_pi_fintype, Fin.sum_univ_two]
    simp [Module.finrank_matrix]
  have hfrPeq : Module.finrank ℂ P = 2 ^ (2 * n + 1) := by
    rw [← eiso.toLinearEquiv.finrank_eq, finrank_eq_two_pow B v, hdim]
  have hk : d 0 = 2 ^ n := by
    have hsum : d 0 * d 0 + d 0 * d 0 = 2 ^ n * 2 ^ n + 2 ^ n * 2 ^ n := by
      have he : d 0 * d 0 + d 1 * d 1 = 2 ^ (2 * n + 1) := hfrP.symm.trans hfrPeq
      rw [← hd01] at he
      rw [he, show 2 * n + 1 = n + n + 1 by ring, pow_succ, pow_add]; ring
    have hd0 : d 0 * d 0 = 2 ^ n * 2 ^ n := by omega
    exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hd0
  have hd1k : d 1 = 2 ^ n := by rw [← hd01]; exact hk

  let pf2 : P ≃ₐ[ℂ] Matrix (Fin (d 0)) (Fin (d 0)) ℂ × Matrix (Fin (d 1)) (Fin (d 1)) ℂ :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo
      (fun i : Fin 2 => Matrix (Fin (d i)) (Fin (d i)) ℂ)) (fun _ => rfl)
  let r0 : Matrix (Fin (d 0)) (Fin (d 0)) ℂ ≃ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr hk)
  let r1 : Matrix (Fin (d 1)) (Fin (d 1)) ℂ ≃ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr hd1k)
  let mEnd : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin (2 ^ n) → ℂ) :=
    LinearMap.toMatrixAlgEquiv'.symm
  refine ⟨Fin (2 ^ n) → ℂ, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · exact eiso.trans (pf2.trans ((AlgEquiv.prodCongr r0 r1).trans (AlgEquiv.prodCongr mEnd mEnd)))

omit [FiniteDimensional ℂ V] in


/-- The Clifford algebra of a symmetric degenerate bilinear form is not semisimple. -/
theorem not_isSemisimpleRing_of_degenerate
    (hsymm : ∀ x y, B x y = B y x) (hdeg : ¬ B.Nondegenerate) :
    ¬ IsSemisimpleRing (BilinearCliffordAlgebra B) := by
  classical
  intro hss

  obtain ⟨v, hv0, hvne⟩ : ∃ v : V, (∀ w, B v w = 0) ∧ v ≠ 0 := by
    rw [LinearMap.BilinForm.Nondegenerate, LinearMap.Nondegenerate, not_and_or] at hdeg
    rcases hdeg with h | h
    · rw [LinearMap.SeparatingLeft] at h
      push Not at h
      obtain ⟨v, hv, hne⟩ := h
      exact ⟨v, hv, hne⟩
    · rw [LinearMap.SeparatingRight] at h
      push Not at h
      obtain ⟨v, hv, hne⟩ := h
      exact ⟨v, fun w => (hsymm v w).trans (hv w), hne⟩
  set Q := quadraticForm B with hQ
  set a : BilinearCliffordAlgebra B := CliffordAlgebra.ι Q v with ha

  have haa : a * a = 0 := by
    have hQv : Q v = 0 := by
      simp only [hQ, quadraticForm, LinearMap.BilinMap.toQuadraticMap_apply]
      exact hv0 v
    rw [ha, CliffordAlgebra.ι_sq_scalar, hQv, map_zero]

  have hanti : ∀ w, a * CliffordAlgebra.ι Q w + CliffordAlgebra.ι Q w * a = 0 := by
    intro w
    have hpolar : QuadraticMap.polar Q v w = 0 := by
      rw [hQ, LinearMap.BilinMap.polar_toQuadraticMap, hv0 w, hsymm w v, hv0 w, add_zero]
    rw [ha, CliffordAlgebra.ι_mul_ι_add_swap, hpolar, map_zero]

  have hkey : ∀ r : BilinearCliffordAlgebra B, a * r = CliffordAlgebra.involute r * a := by
    intro r
    induction r using CliffordAlgebra.induction with
    | algebraMap s => rw [AlgHom.commutes, Algebra.commutes]
    | ι w =>
        rw [CliffordAlgebra.involute_ι, neg_mul]
        exact eq_neg_of_add_eq_zero_left (hanti w)
    | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, map_mul]
    | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

  have hara : ∀ r : BilinearCliffordAlgebra B, a * r * a = 0 := by
    intro r
    rw [hkey r, mul_assoc, haa, mul_zero]


  have hmem : a ∈ Ring.jacobson (BilinearCliffordAlgebra B) := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    refine Ideal.mem_sInf.mpr (fun {M} hM => ?_)
    rw [Set.mem_setOf_eq] at hM
    by_contra haM
    have hlt : M < M ⊔ Ideal.span {a} := by
      refine lt_of_le_of_ne le_sup_left (fun heq => haM ?_)
      have hain : a ∈ M ⊔ Ideal.span {a} :=
        Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
      rwa [← heq] at hain
    have hsup : M ⊔ Ideal.span {a} = ⊤ := (Ideal.isMaximal_def.1 hM).2 _ hlt
    have h1 : (1 : BilinearCliffordAlgebra B) ∈ M ⊔ Ideal.span {a} := hsup ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨m, hmM, n, hn, hmn⟩ := h1
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hn
    have hm_eq : m = 1 - r * a := by
      rw [← hr] at hmn; exact eq_sub_of_add_eq hmn
    have h0 : r * a * r * a = 0 := by
      have e : r * a * r * a = r * (a * r * a) := by noncomm_ring
      rw [e, hara r, mul_zero]
    have hunit : IsUnit m := by
      rw [hm_eq]
      have hval : (1 - r * a) * (1 + r * a) = 1 := by
        have e : (1 - r * a) * (1 + r * a) = 1 - r * a * r * a := by noncomm_ring
        rw [e, h0, sub_zero]
      have hinv : (1 + r * a) * (1 - r * a) = 1 := by
        have e : (1 + r * a) * (1 - r * a) = 1 - r * a * r * a := by noncomm_ring
        rw [e, h0, sub_zero]
      exact ⟨⟨1 - r * a, 1 + r * a, hval, hinv⟩, rfl⟩
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hmM hunit)

  have ha_ne : a ≠ 0 := by
    rw [ha]
    intro h0
    apply hvne
    haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
    have himg : (CliffordAlgebra.equivExterior Q) (CliffordAlgebra.ι Q v)
        = ExteriorAlgebra.ι ℂ v :=
      CliffordAlgebra.changeForm_ι CliffordAlgebra.changeForm.associated_neg_proof v
    have : ExteriorAlgebra.ι ℂ v = 0 := by rw [← himg, h0, map_zero]
    exact (ExteriorAlgebra.ι_eq_zero_iff (R := ℂ) v).1 this
  have hjac : Ring.jacobson (BilinearCliffordAlgebra B) = ⊥ := IsSemisimpleRing.jacobson_eq_bot (BilinearCliffordAlgebra B)
  rw [hjac, Ideal.mem_bot] at hmem
  exact ha_ne hmem


/-- For a symmetric bilinear form on a finite-dimensional complex space, its Clifford algebra is semisimple exactly when the form is nondegenerate. -/
@[source_ref "Chapter3/Problem3.9.5" (role := primary)]
theorem isSemisimpleRing_iff_nondegenerate (hsymm : ∀ x y, B x y = B y x) :
    IsSemisimpleRing (BilinearCliffordAlgebra B) ↔ B.Nondegenerate := by
  refine ⟨fun hss => ?_, fun hnd => isSemisimpleRing_of_nondegenerate B hsymm hnd⟩
  by_contra hdeg
  exact not_isSemisimpleRing_of_degenerate B hsymm hdeg hss


/-- The radical submodule of a complex bilinear form. -/
noncomputable def radical : Submodule ℂ V := LinearMap.ker B

omit [FiniteDimensional ℂ V] in
/-- A vector belongs to the radical submodule of a bilinear form exactly when its associated linear functional is zero. -/
theorem mem_radical_iff {v : V} : v ∈ radical B ↔ B v = 0 := Iff.rfl


/-- The bilinear form induced on the quotient by the radical of a symmetric bilinear form. -/
noncomputable def quotientBilinForm (hsymm : ∀ x y, B x y = B y x) :
    LinearMap.BilinForm ℂ (V ⧸ radical B) :=

  let Bfst : (V ⧸ radical B) →ₗ[ℂ] V →ₗ[ℂ] ℂ := (radical B).liftQ B le_rfl

  let g : V →ₗ[ℂ] (V ⧸ radical B) →ₗ[ℂ] ℂ := Bfst.flip
  ((radical B).liftQ g (by
    intro u hu
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := (radical B).mkQ_surjective w
    change Bfst ((radical B).mkQ v) u = 0

    have h0 : B u = 0 := (mem_radical_iff B).1 hu
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, Bfst]
    rw [hsymm v u, h0, LinearMap.zero_apply])).flip

omit [FiniteDimensional ℂ V] in
/-- The induced quotient form evaluated on quotient classes agrees with the original bilinear form. -/
@[simp]
theorem quotientBilinForm_mkQ (hsymm : ∀ x y, B x y = B y x) (v w : V) :
    quotientBilinForm B hsymm ((radical B).mkQ v) ((radical B).mkQ w) = B v w := by
  simp only [quotientBilinForm, LinearMap.flip_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]

omit [FiniteDimensional ℂ V] in
/-- The bilinear form induced on the quotient by the radical is symmetric. -/
theorem quotientBilinForm_symmetric (hsymm : ∀ x y, B x y = B y x) :
    ∀ x y, quotientBilinForm B hsymm x y = quotientBilinForm B hsymm y x := by
  intro x y
  obtain ⟨v, rfl⟩ := (radical B).mkQ_surjective x
  obtain ⟨w, rfl⟩ := (radical B).mkQ_surjective y
  rw [quotientBilinForm_mkQ, quotientBilinForm_mkQ, hsymm]

omit [FiniteDimensional ℂ V] in
/-- The bilinear form induced on the quotient by the radical is nondegenerate. -/
theorem quotientBilinForm_nondegenerate (hsymm : ∀ x y, B x y = B y x) :
    (quotientBilinForm B hsymm).Nondegenerate := by
  have hL : (quotientBilinForm B hsymm).SeparatingLeft := by
    intro x hx
    obtain ⟨v, rfl⟩ := (radical B).mkQ_surjective x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_radical_iff]
    ext w
    have := hx ((radical B).mkQ w)
    rwa [quotientBilinForm_mkQ] at this
  exact ⟨hL, fun y hy => hL y fun x => by rw [quotientBilinForm_symmetric]; exact hy x⟩

omit [FiniteDimensional ℂ V] in


/-- A generator from the bilinear-form radical commutes past any Clifford element after applying the canonical involution to that element. -/
theorem generator_mul_eq_involute_mul_of_mem_radical (hsymm : ∀ x y, B x y = B y x) {u : V} (hu : u ∈ radical B)
    (z : BilinearCliffordAlgebra B) :
    CliffordAlgebra.ι (quadraticForm B) u * z
      = CliffordAlgebra.involute z * CliffordAlgebra.ι (quadraticForm B) u := by
  induction z using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.commutes]
  | ι y =>
    rw [CliffordAlgebra.involute_ι, neg_mul]
    have hp : QuadraticMap.polar (quadraticForm B) u y = 0 := by
      have h0 : B u = 0 := (mem_radical_iff B).1 hu
      have hu0 : (B u) y = 0 := by rw [h0]; rfl
      have hyu : (B y) u = 0 := by rw [hsymm y u]; exact hu0
      change QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap B) u y = 0
      rw [LinearMap.BilinMap.polar_toQuadraticMap, hu0, hyu, add_zero]
    have hswap := CliffordAlgebra.ι_mul_ι_add_swap (Q := quadraticForm B) u y
    rw [hp, map_zero] at hswap
    exact eq_neg_of_add_eq_zero_left hswap
  | mul a b ha hb =>
    rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc, ← map_mul]
  | add a b ha hb =>
    rw [mul_add, ha, hb, map_add, add_mul]


/-- The quotient map by the radical is an isometry from the original quadratic form to the quadratic form induced by the quotient bilinear form. -/
noncomputable def quotientQuadraticFormIsometry (hsymm : ∀ x y, B x y = B y x) :
    (quadraticForm B) →qᵢ (quadraticForm (quotientBilinForm B hsymm)) where
  toLinearMap := (radical B).mkQ
  map_app' v := by
    change LinearMap.BilinMap.toQuadraticMap (quotientBilinForm B hsymm) ((radical B).mkQ v)
      = LinearMap.BilinMap.toQuadraticMap B v
    rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      quotientBilinForm_mkQ]


/-- The ideal of the Clifford algebra associated with the radical submodule of the bilinear form. -/
noncomputable def radicalIdeal : Ideal (BilinearCliffordAlgebra B) :=
  Ideal.span (CliffordAlgebra.ι (quadraticForm B) '' (radical B : Set V))

omit [FiniteDimensional ℂ V] in
/-- The Clifford generator of a vector in the bilinear-form radical belongs to the associated radical ideal. -/
theorem generator_mem_radicalIdeal_of_mem_radical {u : V} (hu : u ∈ radical B) :
    CliffordAlgebra.ι (quadraticForm B) u ∈ radicalIdeal B :=
  Ideal.subset_span ⟨u, hu, rfl⟩

omit [FiniteDimensional ℂ V] in

/-- For a symmetric bilinear form, the associated radical ideal is two-sided. -/
theorem radicalIdeal_isTwoSided (hsymm : ∀ x y, B x y = B y x) : (radicalIdeal B).IsTwoSided := by

  let T : Submodule (BilinearCliffordAlgebra B) (BilinearCliffordAlgebra B) :=
    { carrier := {x | ∀ c, x * c ∈ radicalIdeal B}
      add_mem' := fun {x y} hx hy c => by rw [add_mul]; exact (radicalIdeal B).add_mem (hx c) (hy c)
      zero_mem' := fun c => by rw [zero_mul]; exact (radicalIdeal B).zero_mem
      smul_mem' := fun r x hx c => by
        rw [smul_eq_mul, mul_assoc]; exact (radicalIdeal B).mul_mem_left r (hx c) }
  have hsub : radicalIdeal B ≤ T := by
    rw [radicalIdeal, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩ c
    rw [generator_mul_eq_involute_mul_of_mem_radical B hsymm hu c]
    exact (radicalIdeal B).mul_mem_left _ (generator_mem_radicalIdeal_of_mem_radical B hu)
  exact ⟨fun {a} b ha => hsub ha b⟩

omit [FiniteDimensional ℂ V] in


/-- For a symmetric form, the kernel of the Clifford-algebra map induced by quotienting by the form radical equals the associated radical ideal. -/
theorem ker_map_quotient_eq_radicalIdeal (hsymm : ∀ x y, B x y = B y x) :
    RingHom.ker (CliffordAlgebra.map (quotientQuadraticFormIsometry B hsymm)).toRingHom = radicalIdeal B := by
  haveI hTS : (radicalIdeal B).IsTwoSided := radicalIdeal_isTwoSided B hsymm
  set φ0 := CliffordAlgebra.map (quotientQuadraticFormIsometry B hsymm) with hφ0
  set mkq := Ideal.Quotient.mkₐ ℂ (radicalIdeal B) with hmkq
  refine le_antisymm ?_ ?_
  ·
    have hker_le : radical B ≤
        LinearMap.ker (mkq.toLinearMap.comp (CliffordAlgebra.ι (quadraticForm B))) := by
      intro u hu
      rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hmkq,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact generator_mem_radicalIdeal_of_mem_radical B hu
    set k := (radical B).liftQ (mkq.toLinearMap.comp (CliffordAlgebra.ι (quadraticForm B)))
      hker_le with hk
    have hkv : ∀ v : V, k ((radical B).mkQ v) = mkq (CliffordAlgebra.ι (quadraticForm B) v) := by
      intro v
      rw [hk, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply]
    have hcond : ∀ w, k w * k w =
        algebraMap ℂ (BilinearCliffordAlgebra B ⧸ radicalIdeal B) (quadraticForm (quotientBilinForm B hsymm) w) := by
      intro w
      obtain ⟨v, rfl⟩ := (radical B).mkQ_surjective w
      have hq : quadraticForm (quotientBilinForm B hsymm) ((radical B).mkQ v) = quadraticForm B v := by
        change LinearMap.BilinMap.toQuadraticMap (quotientBilinForm B hsymm) ((radical B).mkQ v)
          = LinearMap.BilinMap.toQuadraticMap B v
        rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
          quotientBilinForm_mkQ]
      rw [hkv, hq, ← map_mul, CliffordAlgebra.ι_sq_scalar]
      exact mkq.commutes _
    set h := CliffordAlgebra.lift (quadraticForm (quotientBilinForm B hsymm)) ⟨k, hcond⟩ with hh
    have hcomp : h.comp φ0 = mkq := by
      apply CliffordAlgebra.hom_ext
      ext v
      simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, AlgHom.comp_apply]
      rw [hφ0, CliffordAlgebra.map_apply_ι, hh, CliffordAlgebra.lift_ι_apply]
      exact hkv v
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : mkq x = 0 := by
      have hcx := congrArg (fun f : BilinearCliffordAlgebra B →ₐ[ℂ] _ => f x) hcomp
      simp only [AlgHom.comp_apply] at hcx
      rw [← hcx]
      change h (φ0 x) = 0
      rw [show φ0 x = 0 from hx, map_zero]
    rwa [hmkq, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hx0
  ·
    have hsub : (CliffordAlgebra.ι (quadraticForm B) '' (radical B : Set V)) ⊆
        (RingHom.ker φ0.toRingHom : Set (BilinearCliffordAlgebra B)) := by
      rintro _ ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change φ0 (CliffordAlgebra.ι (quadraticForm B) u) = 0
      rw [hφ0, CliffordAlgebra.map_apply_ι]
      have hu0 : (quotientQuadraticFormIsometry B hsymm) u = 0 := by
        change (radical B).mkQ u = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hu
      rw [hu0, map_zero]
    exact Ideal.span_le.mpr hsub

omit [FiniteDimensional ℂ V] in


/-- The Clifford generator of a vector in the bilinear-form radical belongs to the Jacobson radical. -/
theorem generator_mem_jacobson_of_mem_radical (hsymm : ∀ x y, B x y = B y x) {u : V} (hu : u ∈ radical B) :
    CliffordAlgebra.ι (quadraticForm B) u ∈ Ring.jacobson (BilinearCliffordAlgebra B) := by
  set a : BilinearCliffordAlgebra B := CliffordAlgebra.ι (quadraticForm B) u with ha
  have haa : a * a = 0 := by
    have hQu : quadraticForm B u = 0 := by
      have h0 : B u = 0 := (mem_radical_iff B).1 hu
      change LinearMap.BilinMap.toQuadraticMap B u = 0
      rw [LinearMap.BilinMap.toQuadraticMap_apply, h0, LinearMap.zero_apply]
    rw [ha, CliffordAlgebra.ι_sq_scalar, hQu, map_zero]
  have hara : ∀ r : BilinearCliffordAlgebra B, a * r * a = 0 := by
    intro r
    have hkey : a * r = CliffordAlgebra.involute r * a := generator_mul_eq_involute_mul_of_mem_radical B hsymm hu r
    rw [hkey, mul_assoc, haa, mul_zero]
  rw [Ring.jacobson_eq_sInf_isMaximal]
  refine Ideal.mem_sInf.mpr (fun {M} hM => ?_)
  rw [Set.mem_setOf_eq] at hM
  by_contra haM
  have hlt : M < M ⊔ Ideal.span {a} := by
    refine lt_of_le_of_ne le_sup_left (fun heq => haM ?_)
    have hain : a ∈ M ⊔ Ideal.span {a} :=
      Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    rwa [← heq] at hain
  have hsup : M ⊔ Ideal.span {a} = ⊤ := (Ideal.isMaximal_def.1 hM).2 _ hlt
  have h1 : (1 : BilinearCliffordAlgebra B) ∈ M ⊔ Ideal.span {a} := hsup ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at h1
  obtain ⟨m, hmM, n, hn, hmn⟩ := h1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hn
  have hm_eq : m = 1 - r * a := by rw [← hr] at hmn; exact eq_sub_of_add_eq hmn
  have h0 : r * a * r * a = 0 := by
    have e : r * a * r * a = r * (a * r * a) := by noncomm_ring
    rw [e, hara r, mul_zero]
  have hunit : IsUnit m := by
    rw [hm_eq]
    have hval : (1 - r * a) * (1 + r * a) = 1 := by
      have e : (1 - r * a) * (1 + r * a) = 1 - r * a * r * a := by noncomm_ring
      rw [e, h0, sub_zero]
    have hinv : (1 + r * a) * (1 - r * a) = 1 := by
      have e : (1 + r * a) * (1 - r * a) = 1 - r * a * r * a := by noncomm_ring
      rw [e, h0, sub_zero]
    exact ⟨⟨1 - r * a, 1 + r * a, hval, hinv⟩, rfl⟩
  exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hmM hunit)


/-- For a symmetric form on a finite-dimensional complex space, the associated radical ideal equals the Jacobson radical of the Clifford algebra. -/
theorem radicalIdeal_eq_jacobson (hsymm : ∀ x y, B x y = B y x) :
    radicalIdeal B = Ring.jacobson (BilinearCliffordAlgebra B) := by
  refine le_antisymm ?_ ?_
  · change Ideal.span (CliffordAlgebra.ι (quadraticForm B) '' (radical B : Set V)) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact generator_mem_jacobson_of_mem_radical B hsymm hu
  · haveI hss : IsSemisimpleRing (BilinearCliffordAlgebra (quotientBilinForm B hsymm)) :=
      isSemisimpleRing_of_nondegenerate (quotientBilinForm B hsymm) (quotientBilinForm_symmetric B hsymm)
        (quotientBilinForm_nondegenerate B hsymm)
    set φ0 := CliffordAlgebra.map (quotientQuadraticFormIsometry B hsymm) with hφ0
    haveI hsurj : RingHomSurjective φ0.toRingHom :=
      ⟨CliffordAlgebra.map_surjective (quotientQuadraticFormIsometry B hsymm)
        (Submodule.mkQ_surjective (radical B))⟩
    let fsl : BilinearCliffordAlgebra B →ₛₗ[φ0.toRingHom] (BilinearCliffordAlgebra (quotientBilinForm B hsymm)) :=
      { toFun := φ0
        map_add' := map_add φ0
        map_smul' := fun r x => by rw [smul_eq_mul, smul_eq_mul]; exact map_mul φ0 r x }
    have hle := IsSemisimpleModule.jacobson_le_ker (f := fsl)
    rw [← ker_map_quotient_eq_radicalIdeal B hsymm]
    intro x hx
    rw [RingHom.mem_ker]
    have hxk : x ∈ LinearMap.ker fsl := hle hx
    rwa [LinearMap.mem_ker] at hxk


/-- For a symmetric degenerate form on a finite-dimensional space, there is a surjective algebra homomorphism to the Clifford algebra of a symmetric nondegenerate form whose kernel is the Jacobson radical. -/
@[source_ref "Chapter3/Problem3.9.5" (role := supporting)]
theorem exists_surjective_algHom_nondegenerate_quotient_of_degenerate
    (hsymm : ∀ x y, B x y = B y x) (hdeg : ¬ B.Nondegenerate) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (B' : LinearMap.BilinForm ℂ W),
      (∀ x y, B' x y = B' y x) ∧ B'.Nondegenerate ∧
      ∃ φ : BilinearCliffordAlgebra B →ₐ[ℂ] CliffordAlgebra (quadraticForm B'),
        Function.Surjective φ ∧ RingHom.ker φ.toRingHom = Ring.jacobson (BilinearCliffordAlgebra B) := by
  classical
  set U := radical B with hU
  set n := Module.finrank ℂ (V ⧸ U) with hn

  let e : (V ⧸ U) ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ (V ⧸ U)).equivFun
  let B' : LinearMap.BilinForm ℂ (Fin n → ℂ) :=
    (quotientBilinForm B hsymm).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hB'_apply : ∀ x y, B' x y = quotientBilinForm B hsymm (e.symm x) (e.symm y) :=
    fun x y => LinearMap.compl₁₂_apply _ _ _ _ _
  have hB'_symm : ∀ x y, B' x y = B' y x := fun x y => by
    rw [hB'_apply, hB'_apply, quotientBilinForm_symmetric]
  have hL : B'.SeparatingLeft := by
    intro x hx
    have hxr : ∀ w, quotientBilinForm B hsymm (e.symm x) w = 0 := by
      intro w
      have := hx (e w)
      rwa [hB'_apply, LinearEquiv.symm_apply_apply] at this
    have hx0 : e.symm x = 0 := (quotientBilinForm_nondegenerate B hsymm).1 _ hxr
    have := congrArg e hx0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  have hB'_nondeg : B'.Nondegenerate :=
    ⟨hL, fun y hy => hL y fun w => (hB'_symm y w).trans (hy w)⟩

  let eqv : (quadraticForm (quotientBilinForm B hsymm)).IsometryEquiv (quadraticForm B') :=
    { toLinearEquiv := e
      map_app' := fun w => by
        change LinearMap.BilinMap.toQuadraticMap B' (e w)
          = LinearMap.BilinMap.toQuadraticMap (quotientBilinForm B hsymm) w
        rw [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinMap.toQuadraticMap_apply,
          hB'_apply, LinearEquiv.symm_apply_apply] }
  let e_alg := CliffordAlgebra.equivOfIsometry eqv
  set φ0 := CliffordAlgebra.map (quotientQuadraticFormIsometry B hsymm) with hφ0
  refine ⟨Fin n → ℂ, inferInstance, inferInstance, B', hB'_symm, hB'_nondeg,
    e_alg.toAlgHom.comp φ0, ?_, ?_⟩
  ·
    have h0 : Function.Surjective φ0 :=
      CliffordAlgebra.map_surjective _ (Submodule.mkQ_surjective U)
    exact e_alg.surjective.comp h0
  ·
    have hkereq : RingHom.ker (e_alg.toAlgHom.comp φ0).toRingHom = RingHom.ker φ0.toRingHom := by
      ext x
      rw [RingHom.mem_ker, RingHom.mem_ker]
      constructor
      · intro h
        have hx : e_alg (φ0 x) = 0 := h
        exact (map_eq_zero_iff e_alg e_alg.injective).1 hx
      · intro h
        change e_alg (φ0 x) = 0
        rw [show φ0 x = 0 from h, map_zero]
    rw [hkereq, ker_map_quotient_eq_radicalIdeal B hsymm, radicalIdeal_eq_jacobson B hsymm]

end RepresentationTheory.Algebra.CliffordAlgebra.ComplexClassification

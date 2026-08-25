/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Auxiliary.GeneralLinearLocalizationFiltration
import RepresentationTheory.PolynomialRepresentation.Subrepresentation

namespace RepresentationTheory.GL.Weights

open MvPolynomial
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization
open RepresentationTheory.Auxiliary.GeneralLinearLocalizationFiltration
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.LinearAlgebra.Matrix.GeneralLinearGroup.LocalizationAction
open RepresentationTheory.PolynomialRepresentation.Subrepresentation

variable {k : Type} [Field k] {N : ℕ}

/-- A vector lies in the specified weight space exactly when, for every coordinate and unit, the
representation of the displayed group element sends it to scalar multiplication by that unit
raised to the corresponding weight. -/
theorem mem_weightSpace_iff_forall_apply_eq_smul
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (ν : Fin N → ℤ) (v : V) :
    v ∈ integerTupleSubmodule k N ρ ν ↔
      ∀ (i : Fin N) (t : kˣ),
        ρ (diagonalUnit k N i t) v = ((t ^ ν i : kˣ) : k) • v := by
  simp only [integerTupleSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]

/-- Applying the displayed map to an element of the indicated subtype sends source weight-space
membership to target weight-space membership for the same weight. -/
theorem map_mem_weightSpace_of_mem
    (r : ℕ) (x : ↥(localization_degree_filtration k N r)) (ν : Fin N → ℤ)
    (hx : (x : Localization.Away (auxiliary_matrix_polynomial k N)) ∈
      integerTupleSubmodule k N (generalLinearGroupLocalizationRepresentation k N) ν) :
    filtration_to_polynomial_quotient k N r x ∈
      integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N r) ν := by
  rw [mem_weightSpace_iff_forall_apply_eq_smul] at hx ⊢
  intro i t
  rw [← filtration_to_polynomial_quotient_equivariant (diagonalUnit k N i t) r x]
  have hsub :
      (⟨generalLinearGroupLocalizationRepresentation k N (diagonalUnit k N i t)
          (x : Localization.Away (auxiliary_matrix_polynomial k N)),
        localization_degree_filtration_stable (diagonalUnit k N i t) r x.2⟩ :
          ↥(localization_degree_filtration k N r)) =
        ((t ^ ν i : kˣ) : k) • x := by
    apply Subtype.ext
    rw [SetLike.val_smul]
    exact hx i t
  rw [hsub, map_smul]

/-- If a finite family of weight vectors has a span stable under the general linear group action,
then every member of the family lies in the image of the displayed algebra map. -/
theorem mem_range_algebraMap_of_weight_and_span_stable
    [IsAlgClosed k] [CharZero k] {ι : Type*} [Finite ι]
    (w : ι → Localization.Away (auxiliary_matrix_polynomial k N))
    (μ : ι → (Fin N → ℕ))
    (hw : ∀ i, w i ∈ integerTupleSubmodule k N
      (generalLinearGroupLocalizationRepresentation k N) (fun j => (μ i j : ℤ)))
    (hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Submodule.span k (Set.range w),
        generalLinearGroupLocalizationRepresentation k N g x ∈
          Submodule.span k (Set.range w))
    (i : ι) :
    w i ∈ Set.range (algebraMap (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (auxiliary_matrix_polynomial k N))) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set W := Submodule.span k (Set.range w) with hW
  have step : ∀ r : ℕ,
      W ≤ localization_degree_filtration k N (r + 1) →
        W ≤ localization_degree_filtration k N r := by
    intro r hWsucc
    set genElt : ι → ↥(localization_degree_filtration k N (r + 1)) :=
      fun j => ⟨w j, hWsucc (Submodule.subset_span ⟨j, rfl⟩)⟩ with hgenElt
    set Wbar : Submodule k
        (MvPolynomial (Fin N × Fin N) k ⧸ matrixIndexedPolynomialSubmodule k N) :=
      Submodule.span k
        (Set.range (fun j => filtration_to_polynomial_quotient k N (r + 1) (genElt j)))
      with hWbar
    have push : ∀ u ∈ W, ∀ (hu : u ∈ localization_degree_filtration k N (r + 1)),
        filtration_to_polynomial_quotient k N (r + 1) ⟨u, hu⟩ ∈ Wbar := by
      intro u huW
      rw [hW] at huW
      induction huW using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          intro hu
          exact Submodule.subset_span ⟨j, rfl⟩
      | zero =>
          intro hu
          rw [show (⟨(0 : Localization.Away (auxiliary_matrix_polynomial k N)), hu⟩ :
              ↥(localization_degree_filtration k N (r + 1))) = 0 from rfl, map_zero]
          exact Submodule.zero_mem Wbar
      | add x y hx hy ihx ihy =>
          intro hu
          have hux : x ∈ localization_degree_filtration k N (r + 1) :=
            hWsucc (by rw [hW]; exact hx)
          have huy : y ∈ localization_degree_filtration k N (r + 1) :=
            hWsucc (by rw [hW]; exact hy)
          have hsplit :
              (⟨x + y, hu⟩ : ↥(localization_degree_filtration k N (r + 1))) =
                ⟨x, hux⟩ + ⟨y, huy⟩ := rfl
          rw [hsplit, map_add]
          exact Submodule.add_mem _ (ihx hux) (ihy huy)
      | smul c x hx ihx =>
          intro hu
          have hux : x ∈ localization_degree_filtration k N (r + 1) :=
            hWsucc (by rw [hW]; exact hx)
          have hsplit :
              (⟨c • x, hu⟩ : ↥(localization_degree_filtration k N (r + 1))) =
                c • ⟨x, hux⟩ := rfl
          rw [hsplit, map_smul]
          exact Submodule.smul_mem _ _ (ihx hux)
    have hinv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
        ∀ y ∈ Wbar, naturalIndexedQuotientRepresentation k N (r + 1) g y ∈ Wbar := by
      intro g y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j, rfl⟩ := hz
          rw [← filtration_to_polynomial_quotient_equivariant g (r + 1) (genElt j)]
          exact push _
            (hstable g (w j) (by rw [hW]; exact Submodule.subset_span ⟨j, rfl⟩)) _
      | zero => rw [map_zero]; exact Submodule.zero_mem Wbar
      | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
      | smul c a _ iha => rw [map_smul]; exact Submodule.smul_mem _ _ iha
    have hnn : Wbar ≤ ⨆ (ν : Fin N → ℕ),
        integerTupleSubmodule k N (naturalIndexedQuotientRepresentation k N (r + 1))
          (fun l => (ν l : ℤ)) := by
      rw [hWbar, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.mem_iSup_of_mem (μ j)
        (map_mem_weightSpace_of_mem (r + 1) (genElt j) _ (hw j))
    have hWbar_bot : Wbar = ⊥ :=
      submodule_eq_bot_of_invariant_of_le_iSup k N (r + 1) (by omega) hinv hnn
    have hgen : ∀ j, w j ∈ localization_degree_filtration k N r := by
      intro j
      have hwj : w j ∈ localization_degree_filtration k N (r + 1) :=
        hWsucc (Submodule.subset_span ⟨j, rfl⟩)
      have hquot : filtration_to_polynomial_quotient k N (r + 1) ⟨w j, hwj⟩ = 0 := by
        have hmem := push (w j) (Submodule.subset_span ⟨j, rfl⟩) hwj
        rw [hWbar_bot] at hmem
        simpa using hmem
      have hker : (⟨w j, hwj⟩ : ↥(localization_degree_filtration k N (r + 1))) ∈
          LinearMap.ker (filtration_to_polynomial_quotient k N (r + 1)) :=
        LinearMap.mem_ker.2 hquot
      rw [ker_filtration_to_polynomial_quotient (r + 1) (by omega)] at hker
      simpa using hker
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hgen)
  have descend : ∀ r : ℕ,
      W ≤ localization_degree_filtration k N r →
        W ≤ localization_degree_filtration k N 0 := by
    intro r
    induction r with
    | zero => exact id
    | succ r ih => intro h; exact ih (step r h)
  have hWR : W ≤ localization_degree_filtration k N
      (Finset.univ.sup (fun j => localization_denominator_order (w j))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_localization_degree_filtration_iff_order_le]
    exact Finset.le_sup (f := fun j => localization_denominator_order (w j))
      (Finset.mem_univ j)
  have hW0 : W ≤ localization_degree_filtration k N 0 := descend _ hWR
  have hwi0 : w i ∈ localization_degree_filtration k N 0 :=
    hW0 (Submodule.subset_span ⟨i, rfl⟩)
  rw [mem_localization_degree_filtration_iff_order_le] at hwi0
  exact (denominator_order_eq_zero_iff_mem_range_algebraMap (w i)).mp
    (Nat.le_zero.mp hwi0)

/-- Under the stated weight and span-stability assumptions, for each index there is a polynomial
whose evaluation at the entries of any invertible matrix equals the displayed function associated
with that family member. -/
theorem exists_polynomial_eval_apply_of_weight_and_span_stable
    [IsAlgClosed k] [CharZero k] {ι : Type*} [Finite ι]
    (w : ι → Localization.Away (auxiliary_matrix_polynomial k N))
    (μ : ι → (Fin N → ℕ))
    (hw : ∀ i, w i ∈ integerTupleSubmodule k N
      (generalLinearGroupLocalizationRepresentation k N) (fun j => (μ i j : ℤ)))
    (hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Submodule.span k (Set.range w),
        generalLinearGroupLocalizationRepresentation k N g x ∈
          Submodule.span k (Set.range w))
    (i : ι) :
    ∃ Q : MvPolynomial (Fin N × Fin N) k,
      ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
        localization_evaluation_ringHom (w i) g =
          MvPolynomial.eval
            (fun ij : Fin N × Fin N =>
              (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q := by
  obtain ⟨Q, hQ⟩ := mem_range_algebraMap_of_weight_and_span_stable w μ hw hstable i
  refine ⟨Q, fun g => ?_⟩
  rw [← hQ, localization_evaluation_algebraMap, matrix_polynomial_evaluation_apply]

/-- Under the stated weight and span-stability assumptions, for each index there is a polynomial
whose evaluation at the entries of any invertible matrix equals the displayed expression involving
that matrix and family member. -/
theorem exists_polynomial_eval_matrixEntries_of_weight_and_span_stable
    [IsAlgClosed k] [CharZero k] {ι : Type*} [Finite ι]
    (P : ι → MvPolynomial (AuxiliaryIndex N) k) (μ : ι → (Fin N → ℕ))
    (hw : ∀ i, auxiliary_localization_ringHom (P i) ∈
      integerTupleSubmodule k N (generalLinearGroupLocalizationRepresentation k N)
        (fun j => (μ i j : ℤ)))
    (hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ x ∈ Submodule.span k
        (Set.range fun i => auxiliary_localization_ringHom (P i)),
      generalLinearGroupLocalizationRepresentation k N g x ∈
        Submodule.span k (Set.range fun i => auxiliary_localization_ringHom (P i)))
    (i : ι) :
    ∃ Q : MvPolynomial (Fin N × Fin N) k,
      ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
        auxiliaryPolynomialEvaluation g (P i) =
          MvPolynomial.eval
            (fun ij : Fin N × Fin N =>
              (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_eval_apply_of_weight_and_span_stable
    (fun i => auxiliary_localization_ringHom (P i)) μ hw hstable i
  refine ⟨Q, fun g => ?_⟩
  rw [auxiliary_localization_ringHom_action_apply, hQ]

end RepresentationTheory.GL.Weights

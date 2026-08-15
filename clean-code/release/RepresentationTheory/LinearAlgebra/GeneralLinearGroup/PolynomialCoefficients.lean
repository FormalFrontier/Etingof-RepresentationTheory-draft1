/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
import RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation

open scoped TensorProduct
open MvPolynomial Matrix

noncomputable section

open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
open RepresentationTheory.GeneralLinear.AuxiliaryPolynomialEmbedding
open RepresentationTheory.GeneralLinear.AuxiliaryRepresentationFamilies
open RepresentationTheory.GeneralLinear.HomogeneousPolynomialsAndAuxiliaryRepresentations
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.PolynomialQuotientRepresentation
open RepresentationTheory.Matrix.MvPolynomialRightMul.Matrix
open RepresentationTheory.MatrixPolynomialHomogeneity

namespace RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

/-- The predicate is transferred along a surjective linear map that intertwines the two indexed
families of linear maps. -/
theorem of_surjective_intertwining {k : Type*} [Field k] {N : ℕ}
    {Y Z : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Z] [Module k Z] [Module.Finite k Z]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {σ : Matrix.GeneralLinearGroup (Fin N) k → Z →ₗ[k] Z}
    (π : Y →ₗ[k] Z) (hπ_surj : Function.Surjective π)
    (hcomm : ∀ g y, π (ρ g y) = σ g (π y))
    (h : HasAuxiliaryMapProperty N ρ) :
    HasAuxiliaryMapProperty N σ := by
  classical
  obtain ⟨M, B, P, hP⟩ := h
  let b' : Module.Basis (Fin (Module.finrank k Z)) k Z := Module.finBasis k Z
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ_surj)
  have hsec : ∀ z, π (s z) = z := fun z => by
    have := LinearMap.congr_fun hs z; simpa using this
  refine ⟨Module.finrank k Z, b',
    fun a c => ∑ d, ∑ e,
      MvPolynomial.C (B.repr (s (b' c)) d) * P e d
        * MvPolynomial.C (b'.repr (π (B e)) a), fun g a c => ?_⟩
  let φ : Y →ₗ[k] k := (Finsupp.lapply a).comp (b'.repr.toLinearMap.comp π)
  have hφ_apply : ∀ y, φ y = b'.repr (π y) a := fun _ => rfl
  have hkey : π (ρ g (s (b' c))) = σ g (b' c) := by rw [hcomm, hsec]
  have hlhs : b'.repr (σ g (b' c)) a
      = ∑ d, ∑ e, B.repr (s (b' c)) d
          * (auxiliaryPolynomialEvaluation g (P e d) * b'.repr (π (B e)) a) := by
    rw [show b'.repr (σ g (b' c)) a = φ (ρ g (s (b' c))) from by rw [hφ_apply, hkey]]
    rw [show ρ g (s (b' c))
        = ∑ d, B.repr (s (b' c)) d • ρ g (B d) from by
      conv_lhs => rw [show s (b' c) = ∑ d, B.repr (s (b' c)) d • B d from
        (B.sum_repr (s (b' c))).symm]
      rw [map_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [map_smul]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, smul_eq_mul]
    have hd : φ (ρ g (B d))
        = ∑ e, auxiliaryPolynomialEvaluation g (P e d) * b'.repr (π (B e)) a := by
      conv_lhs => rw [show ρ g (B d) = ∑ e, B.repr (ρ g (B d)) e • B e from
        (B.sum_repr (ρ g (B d))).symm]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, smul_eq_mul, hP g e d, hφ_apply]
    rw [hd, Finset.mul_sum]
  rw [hlhs, evaluate_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evaluate_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [evaluate_mul, evaluate_mul, evaluate_C, evaluate_C]
  ring

end RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty

namespace RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients

/-- The multivariate polynomial associated to two finitely supported families of natural-number
exponents. -/
noncomputable def multiIndexPolynomial (k : Type*) [Field k] (N : ℕ)
    (s t : (Fin N × Fin N) →₀ ℕ) : MvPolynomial (AuxiliaryIndex N) k :=
  MvPolynomial.coeff t
    (mvPolynomialRightMul
      (Matrix.of fun l j : Fin N => MvPolynomial.X (R := k) (Sum.inl (l, j)))
      (MvPolynomial.monomial s (1 : MvPolynomial (AuxiliaryIndex N) k)))

/-- Relates an evaluation involving the polynomial indexed by two exponent families to the
coefficient indexed by the second family after applying the given map to the monomial indexed by
the first. -/
theorem coeff_apply_monomial {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) (s t : (Fin N × Fin N) →₀ ℕ) :
    auxiliaryPolynomialEvaluation g (multiIndexPolynomial k N s t)
      = MvPolynomial.coeff t
          (generalLinearGroupMvPolynomialRightMul k N g
            (MvPolynomial.monomial s (1 : k))) := by
  classical
  set R := MvPolynomial (AuxiliaryIndex N) k with hR
  set eHom : R →+* k :=
    MvPolynomial.eval
      (Sum.elim
        (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (fun _ => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)) with heHom
  set Ggen : Matrix (Fin N) (Fin N) R :=
    Matrix.of fun l j => MvPolynomial.X (Sum.inl (l, j)) with hGgen
  have hnat : ∀ p : MvPolynomial (Fin N × Fin N) R,
      MvPolynomial.map eHom (mvPolynomialRightMul Ggen p)
        = mvPolynomialRightMul (g : Matrix (Fin N) (Fin N) k) (MvPolynomial.map eHom p) := by
    have hring :
        (MvPolynomial.map eHom).comp (mvPolynomialRightMul Ggen).toRingHom
          = (mvPolynomialRightMul (g : Matrix (Fin N) (Fin N) k)).toRingHom.comp
              (MvPolynomial.map eHom) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          mvPolynomialRightMul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
          MvPolynomial.map_C]
      · intro ij
        obtain ⟨i, j⟩ := ij
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          mvPolynomialRightMul_apply_X, MvPolynomial.map_X, hGgen, Matrix.of_apply,
          MvPolynomial.smul_eq_C_mul, map_sum, map_mul, MvPolynomial.map_C,
          MvPolynomial.map_X]
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 2
        rw [heHom, MvPolynomial.eval_X, Sum.elim_inl]
    have := RingHom.congr_fun hring
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using this
  rw [generalLinearGroupMvPolynomialRightMul_apply]
  have hmon : (MvPolynomial.monomial s (1 : k))
      = MvPolynomial.map eHom (MvPolynomial.monomial s (1 : R)) := by
    rw [MvPolynomial.map_monomial]
    congr 1
    exact (map_one eHom).symm
  rw [hmon, ← hnat, MvPolynomial.coeff_map]
  rfl

/-- The family of linear maps obtained from the ρ field of the finite-dimensional representation
satisfies the ambient predicate. -/
theorem fdRep_rho_satisfies_property (k : Type*) [Field k] (N d : ℕ) :
    HasAuxiliaryMapProperty N (auxiliaryIndexedGeneralLinearFDRep k N d).ρ := by
  classical
  set S : Finset ((Fin N × Fin N) →₀ ℕ) := Finset.univ.finsuppAntidiag d with hS
  have hmem : ∀ s : {s // s ∈ S},
      (MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k))
        ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d := by
    intro s
    exact monomial_mem_homogeneousSubmodule d _
      (Finset.mem_finsuppAntidiag.mp (hS ▸ s.2)).1
  let v : {s // s ∈ S} → auxiliaryIndexedGeneralLinearFDRep k N d :=
    fun s => ⟨MvPolynomial.monomial (↑s) 1, by
      rw [homogeneousSubrepresentation_toSubmodule]; exact hmem s⟩
  have hpolyv : ∀ s,
      auxiliaryPolynomialEmbedding d (v s) =
        MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) :=
    fun _ => rfl
  have hli : LinearIndependent k v := by
    have hb : LinearIndependent k (fun s : {s // s ∈ S} =>
        MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k)) := by
      have hcomp := (basisMonomials (Fin N × Fin N) k).linearIndependent.comp
        (fun s : {s // s ∈ S} => (↑s : (Fin N × Fin N) →₀ ℕ))
          Subtype.val_injective
      simpa only [Function.comp_def, coe_basisMonomials] using hcomp
    exact hb.of_comp (auxiliaryPolynomialEmbedding d)
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rintro w -
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun s => MvPolynomial.coeff (↑s) (auxiliaryPolynomialEmbedding d w),
      auxiliaryPolynomialEmbedding_injective d ?_⟩
    have hsupp : ∀ p ∈ (auxiliaryPolynomialEmbedding d w).support, p ∈ S := by
      intro p hp
      rw [hS, Finset.mem_finsuppAntidiag]
      refine ⟨?_, Finset.subset_univ _⟩
      have hH : (auxiliaryPolynomialEmbedding d w).IsHomogeneous d :=
        auxiliaryPolynomialEmbedding_mem_homogeneousSubmodule d w
      have hd := hH (MvPolynomial.mem_support_iff.mp hp)
      calc ∑ i, p i = p.degree := (Finsupp.degree_eq_sum p).symm
        _ = Finsupp.weight (fun _ => 1) p := by rw [Finsupp.degree_eq_weight_one]
        _ = d := hd
    rw [map_sum]
    simp_rw [map_smul, hpolyv]
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach S
      (fun p => MvPolynomial.coeff p (auxiliaryPolynomialEmbedding d w) •
        MvPolynomial.monomial p (1 : k))]
    simp_rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
    conv_rhs => rw [(auxiliaryPolynomialEmbedding d w).as_sum]
    refine (Finset.sum_subset hsupp ?_).symm
    intro p _ hp
    rw [MvPolynomial.notMem_support_iff.mp hp]
    exact MvPolynomial.monomial_zero
  let b : Module.Basis {s // s ∈ S} k (auxiliaryIndexedGeneralLinearFDRep k N d) :=
    Module.Basis.mk hli hsp
  have hbv : ∀ s,
      auxiliaryPolynomialEmbedding d (b s) =
        MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) := by
    intro s; rw [show b s = v s from Module.Basis.mk_apply hli hsp s]; exact hpolyv s
  have hrepr : ∀ (w : auxiliaryIndexedGeneralLinearFDRep k N d) (a : {s // s ∈ S}),
      b.repr w a = MvPolynomial.coeff (↑a) (auxiliaryPolynomialEmbedding d w) := by
    intro w a
    have hexp : auxiliaryPolynomialEmbedding d w
        = ∑ s : {s // s ∈ S}, b.repr w s •
            MvPolynomial.monomial (↑s : (Fin N × Fin N) →₀ ℕ) (1 : k) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl fun s _ => by rw [map_smul, hbv s]
    rw [hexp, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single a
      (fun s _ hsa => by rw [if_neg (fun h => hsa (Subtype.ext h)), mul_zero])
      (fun ha => absurd (Finset.mem_univ a) ha)]
    rw [if_pos rfl, mul_one]
  refine ⟨Fintype.card {s // s ∈ S}, b.reindex (Fintype.equivFin {s // s ∈ S}),
    fun a c => multiIndexPolynomial k N (↑((Fintype.equivFin {s // s ∈ S}).symm c))
      (↑((Fintype.equivFin {s // s ∈ S}).symm a)), fun g a c => ?_⟩
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, hrepr,
    auxiliaryPolynomialEmbedding_groupAction, hbv, coeff_apply_monomial]

/-- The family of linear maps obtained from the ρ field of the finite-dimensional representation
satisfies the ambient predicate. -/
theorem fdRep_rho_satisfies_property' (k : Type*) [Field k] (N d : ℕ) :
    HasAuxiliaryMapProperty N (auxiliaryRepresentationFamilyOne k N d).ρ := by
  have hmem_π : ∀ x ∈ MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d,
      Submodule.mkQ (matrixIndexedPolynomialSubmodule k N) x
        ∈ (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d).map
            (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)) :=
    fun x hx => Submodule.mem_map_of_mem hx
  let πmap : auxiliaryIndexedGeneralLinearFDRep k N d →ₗ[k]
      auxiliaryRepresentationFamilyOne k N d :=
    (Submodule.mkQ (matrixIndexedPolynomialSubmodule k N)).restrict hmem_π
  refine HasAuxiliaryMapProperty.of_surjective_intertwining πmap ?_ ?_
    (fdRep_rho_satisfies_property k N d)
  · rintro ⟨_, f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, Subtype.ext rfl⟩
  · intro g v
    apply Subtype.ext
    change Submodule.mkQ _
        (generalLinearGroupMvPolynomialRightMul k N g (auxiliaryPolynomialEmbedding d v)) =
      matrixPolynomialQuotientRepresentation k N g
        (Submodule.mkQ _ (auxiliaryPolynomialEmbedding d v))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      matrixPolynomialQuotientRepresentation_apply_mk]

end RepresentationTheory.LinearAlgebra.GeneralLinearGroup.PolynomialCoefficients

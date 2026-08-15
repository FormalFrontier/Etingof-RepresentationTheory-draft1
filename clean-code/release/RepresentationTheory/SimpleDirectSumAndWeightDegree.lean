/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinear.AuxiliaryDecomposition

open CategoryTheory MvPolynomial DirectSum

noncomputable section

namespace RepresentationTheory.SimpleDirectSumAndWeightDegree

open RepresentationTheory.AsModuleEquivalences
open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
open RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition
open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.GeneralLinear.AuxiliaryDecomposition
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
open RepresentationTheory.SymmetricPolynomials.Alternant

namespace SimpleModule

variable {R : Type*} [Ring R]

/-- A simple module admitting an injective linear map into a finite direct sum of simple
modules is linearly equivalent to one of the summands. -/
theorem exists_linearEquiv_summand_of_injective_to_directSum
    {ι : Type*} [Finite ι] (L : ι → Type*)
    [∀ i, AddCommGroup (L i)] [∀ i, Module R (L i)]
    (hsimp : ∀ i, IsSimpleModule R (L i))
    {T : Type*} [AddCommGroup T] [Module R T] [IsSimpleModule R T]
    (ψ : T →ₗ[R] DirectSum ι L) (hψ : Function.Injective ψ) :
    ∃ i, Nonempty (T ≃ₗ[R] L i) := by
  classical
  set Tsub : Submodule R (DirectSum ι L) := LinearMap.range ψ with hTsub
  have eT : T ≃ₗ[R] Tsub := LinearEquiv.ofInjective ψ hψ
  haveI : IsSimpleModule R Tsub := (LinearEquiv.isSimpleModule_iff eT).mp ‹_›
  set cs : Set (Submodule R (DirectSum ι L)) :=
    Set.range (fun i => LinearMap.range (DirectSum.lof R ι L i)) with hcs
  have hlof_inj : ∀ i, Function.Injective (DirectSum.lof R ι L i) := fun i =>
    Function.LeftInverse.injective (g := DirectSum.component R ι L i)
      (fun b => DirectSum.component.lof_self R i b)
  have hcs_simple : ∀ m : cs, IsSimpleModule R (m : Submodule R (DirectSum ι L)) := by
    rintro ⟨m, i, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hlof_inj i)).symm
  haveI := hcs_simple
  have hcs_top : sSup cs = ⊤ := by
    rw [hcs, sSup_range]
    exact DFinsupp.iSup_range_lsingle
  have hTle : Tsub ≤ sSup cs := by rw [hcs_top]; exact le_top
  obtain ⟨m, hm, ⟨e'⟩⟩ := Tsub.linearEquiv_of_le_sSup cs hTle
  obtain ⟨i, rfl⟩ := hm
  exact ⟨i, ⟨eT.trans (e'.trans (LinearEquiv.ofInjective _ (hlof_inj i)).symm)⟩⟩

end SimpleModule

namespace GeneralLinearRepresentation

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- For a representation whose nonzero weights have a fixed coordinate sum, an injectively
embedded simple representation has invariant equal to a positively occurring term in any
specified finite polynomial expansion. -/
theorem exists_positive_polynomial_term_of_simple_subrepresentation_of_weightSum (N n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n)
    (S : Finset {l : Fin N → ℕ // Antitone l})
    (c : {l : Fin N → ℕ // Antitone l} → ℕ)
    (hchar : weightCharacter k N M =
      ∑ ν ∈ S, (c ν : ℚ) • partitionPolynomial N ν.val)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] M)
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = M.ρ g (φ v)) :
    ∃ ν ∈ S, 0 < c ν ∧ weightCharacter k N L = partitionPolynomial N ν.val := by
  classical
  obtain ⟨ι, hιFin, hιDec, Sm, hSacg, hSmod, hSfin, Lf, hLfsimp, hLfdist, hSne, e, he,
      p, f, ⟨eM⟩⟩ :=
    existsLinearEquivFiniteDirectSum k N n M halg h_span h_homog
  letI := hιFin; letI := hιDec
  letI : ∀ i, AddCommGroup (Sm i) := hSacg
  letI : ∀ i, Module k (Sm i) := hSmod
  letI : ∀ i, Module.Finite k (Sm i) := hSfin
  obtain ⟨lam_cl, lam_inj, hchar_cl⟩ :=
    exists_injective_auxiliaryLabeling k N n Lf e he hLfsimp hLfdist hSne
  have hφM : Representation.asModule M.ρ
      ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (Representation.directSum (fun j : Fin p => (Lf (f j)).ρ)) :=
    eM ≪≫ₗ (directSumAsModuleEquiv (fun j : Fin p => (Lf (f j)).ρ)).symm
  have hM_sum : weightCharacter k N M =
      ∑ j : Fin p, partitionPolynomial N (lam_cl (f j)).val := by
    have hchar_eq : weightCharacter k N M
        = weightCharacter k N
          (FDRep.of (Representation.directSum (fun j : Fin p => (Lf (f j)).ρ))) := by
      have h0 := auxiliaryPolynomial_eq_of_linearEquiv k N M.ρ
        (Representation.directSum (fun j : Fin p => (Lf (f j)).ρ))
        (representationLinearEquiv hφM)
        (fun g v => representationLinearEquiv_intertwines hφM g v)
      rwa [auxiliary_fdRep_value_of_representation_eq] at h0
    rw [hchar_eq,
      auxiliaryPolynomial_directSum k N (fun j : Fin p => (Lf (f j) : Type))
        (fun j : Fin p => (Lf (f j)).ρ)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [auxiliary_fdRep_value_of_representation_eq, hchar_cl (f j)]
  haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ) := hLsimp
  let φR : Representation.asModule L.ρ
      →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)] Representation.asModule M.ρ :=
    linearMapAsModule φ hφ_equiv
  have hφRinj : Function.Injective φR := hφ_inj
  let ψ : Representation.asModule L.ρ
      →ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        DirectSum (Fin p) (fun j => Representation.asModule (Lf (f j)).ρ) :=
    eM.toLinearMap ∘ₗ φR
  have hψinj : Function.Injective ψ := eM.injective.comp hφRinj
  obtain ⟨j₀, ⟨eLj⟩⟩ :=
    SimpleModule.exists_linearEquiv_summand_of_injective_to_directSum
      (R := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (fun j : Fin p => Representation.asModule (Lf (f j)).ρ)
      (fun j => hLfsimp (f j)) ψ hψinj
  set x : {l : Fin N → ℕ // Antitone l} := lam_cl (f j₀) with hx
  have hcharL : weightCharacter k N L = partitionPolynomial N x.val := by
    have h0 := auxiliaryPolynomial_eq_of_linearEquiv k N L.ρ (Lf (f j₀)).ρ
      (representationLinearEquiv eLj)
      (fun g v => representationLinearEquiv_intertwines eLj g v)
    rw [auxiliary_fdRep_value_of_representation_eq,
      auxiliary_fdRep_value_of_representation_eq] at h0
    rw [h0, hchar_cl (f j₀)]
  have hcoeff : (∑ j : Fin p, Finsupp.single (lam_cl (f j)) (1 : ℚ))
      = ∑ ν ∈ S, Finsupp.single ν (c ν : ℚ) := by
    apply auxiliaryPolynomial_linearIndependent N
    rw [map_sum, map_sum]
    simp only [Finsupp.linearCombination_single, one_smul]
    rw [← hM_sum, hchar]
  have hLHSpos : 0 < (∑ j : Fin p, Finsupp.single (lam_cl (f j)) (1 : ℚ)) x := by
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨j₀, Finset.mem_univ _, ?_⟩
    · rw [Finsupp.single_apply]; split <;> norm_num
    · rw [Finsupp.single_apply, if_pos hx.symm]; norm_num
  rw [hcoeff, Finsupp.finsetSum_apply] at hLHSpos
  simp only [Finsupp.single_apply] at hLHSpos
  rw [Finset.sum_ite_eq' S x (fun ν => (c ν : ℚ))] at hLHSpos
  by_cases hxS : x ∈ S
  · rw [if_pos hxS] at hLHSpos
    exact ⟨x, hxS, by exact_mod_cast hLHSpos, hcharL⟩
  · rw [if_neg hxS] at hLHSpos
    exact absurd hLHSpos (lt_irrefl 0)

end GeneralLinearRepresentation

end RepresentationTheory.SimpleDirectSumAndWeightDegree

end

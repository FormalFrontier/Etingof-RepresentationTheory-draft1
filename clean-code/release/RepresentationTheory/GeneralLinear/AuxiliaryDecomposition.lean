/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Module.IndexedCoordinateProjections
import RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
import RepresentationTheory.UnitTupleActions
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition
import RepresentationTheory.GeneralLinear.InvariantSubtype
import RepresentationTheory.Auxiliary.LinearIndependence
import RepresentationTheory.Algebra.Module.Simple
import RepresentationTheory.AuxiliaryGeneralLinearTrace

namespace RepresentationTheory.GeneralLinear.AuxiliaryDecomposition

open CategoryTheory MvPolynomial
open scoped TensorProduct
open RepresentationTheory.Algebra.Module.Simple
open RepresentationTheory.AsModuleEquivalences
open RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
open RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.AuxiliaryCharacter
open RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.Representation.ModuleEquivAndTraceSeparation
open RepresentationTheory.SymmetricPolynomials.Alternant
open RepresentationTheory.UnitTupleActions

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- A surjective equivariant linear map transfers the displayed auxiliary supremum-equals-top
property to its target. -/
theorem auxiliarySup_eq_top_of_surjective_equivariant (N : ℕ)
    (M P : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (φ : M →ₗ[k] P)
    (hφ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : M), φ (M.ρ g v) = P.ρ g (φ v))
    (hsurj : Function.Surjective φ)
    (hM : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ (μ : Fin N →₀ ℕ), weightSpace k N P (fun i => μ i) = ⊤ := by
  have hmap : ∀ μ : Fin N →₀ ℕ,
      Submodule.map φ (weightSpace k N M (fun i => μ i))
        ≤ weightSpace k N P (fun i => μ i) := by
    intro μ
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    simp only [Submodule.mem_comap, weightSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
    intro i t
    rw [← hφ, hv i t, map_smul]
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hsurj, ← Submodule.map_top, ← hM,
    Submodule.map_iSup]
  exact iSup_mono hmap

omit [CharZero k] in
/-- The displayed auxiliary supremum for the auxiliary representation indexed by a
natural-valued tuple is top. -/
theorem auxiliarySup_eq_top_for_auxiliaryRepresentation (N : ℕ) (lam : Fin N → ℕ) :
    ⨆ (μ : Fin N →₀ ℕ),
      weightSpace k N (schurRepresentation k N lam) (fun i => μ i) = ⊤ := by
  refine auxiliarySup_eq_top_of_surjective_equivariant k N
    (FDRep.of (tensorPowerRepresentation k N (∑ i, lam i))) (schurRepresentation k N lam)
    (LinearMap.rangeRestrict (symmetrizerEndomorphism k N lam)) ?_
    (LinearMap.surjective_rangeRestrict _)
    (auxiliaryRepresentation_iSupWeightSpace_eq_top k N (∑ i, lam i))
  intro g v
  apply Subtype.ext
  change symmetrizerEndomorphism k N lam
      ((FDRep.of (tensorPowerRepresentation k N (∑ i, lam i))).ρ g v)
     = (tensorPowerRepresentation k N (∑ i, lam i) g) (symmetrizerEndomorphism k N lam v)
  rw [FDRep.of_ρ']
  exact (LinearMap.ext_iff.mp
    (tensorPowerRepresentation_comp_symmetrizerEndomorphism k N lam g) v).symm

/-- An equivariant direct-sum decomposition yields the displayed equality between weighted
sums of auxiliary values. -/
theorem weightedAuxiliaryValue_sum_eq
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v)) :
    ∑ i : ι, (Module.finrank k (S i) : ℚ) • weightCharacter k N (L i) =
      ∑ lam : FinPartition N n,
        (Module.finrank ℂ (partitionSubmodule n
          (lam.sum_parts ▸ partitionOfTuple N lam.parts)) : ℚ) •
        partitionPolynomial N lam.parts := by
  have h1 : weightCharacter k N (FDRep.of (tensorPowerRepresentation k N n)) =
      ∑ i : ι, (Module.finrank k (S i) : ℚ) • weightCharacter k N (L i) := by
    rw [auxiliaryPolynomial_eq_of_linearEquiv k N (tensorPowerRepresentation k N n)
        (Representation.directSum (fun i =>
          (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
            (S i)).tprod (L i).ρ)) e he,
      auxiliaryPolynomial_directSum]
    exact Finset.sum_congr rfl (fun i _ => auxiliaryPolynomial_trivialTensor k N (S i) (L i))
  rw [← h1, auxiliaryRepresentation_polynomial_eq_sum_X_pow,
    sum_variables_pow_eq_sum_finrank_smul]

/-- An auxiliary definition whose formal type is unavailable. -/
noncomputable def auxiliaryDefinition
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v)) :
    Representation.asModule (tensorPowerRepresentation k N n) ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k)]
      DirectSum (Σ i : ι, Fin (Module.finrank k (S i)))
        (fun ν => Representation.asModule (L ν.1).ρ) :=
  (linearEquivAsModule e he) ≪≫ₗ
    (directSumAsModuleEquiv
      (fun i => (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (S i)).tprod (L i).ρ)) ≪≫ₗ
    (DFinsupp.mapRange.linearEquiv (fun i =>
      trivialTensorAsModuleEquiv (Module.finBasis k (S i)) (L i).ρ)) ≪≫ₗ
    (DirectSum.sigmaLcurryEquiv (R := MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k))
      (δ := fun (i : ι) (_ : Fin (Module.finrank k (S i))) =>
        Representation.asModule (L i).ρ)).symm

/-- The displayed auxiliary values agree when the associated representation modules are
linearly equivalent. -/
theorem auxiliaryValue_eq_of_linearEquiv
    (k : Type) [Field k] [IsAlgClosed k] (N : ℕ)
    {V W : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (σ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (Φ : Representation.asModule ρ ≃ₗ[MonoidAlgebra k
        (Matrix.GeneralLinearGroup (Fin N) k)] Representation.asModule σ) :
    weightCharacter k N (FDRep.of ρ) = weightCharacter k N (FDRep.of σ) := by
  set ek : V ≃ₗ[k] W :=
    ρ.asModuleEquiv.symm ≪≫ₗ Φ.restrictScalars k ≪≫ₗ σ.asModuleEquiv with hek
  refine auxiliaryPolynomial_eq_of_linearEquiv k N ρ σ ek ?_
  intro g v
  simp only [hek, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

open DirectSum in
/-- A simple module embedded in a finite direct sum of simple modules is linearly equivalent
to one of the summands. -/
theorem simpleModule_linearEquiv_directSummand
    {R : Type*} [Ring R] {W : Type*} [AddCommGroup W] [Module R W]
    {κ : Type*} [Finite κ] (Lsum : κ → Type*)
    [∀ c, AddCommGroup (Lsum c)] [∀ c, Module R (Lsum c)]
    (hsimp : ∀ c, IsSimpleModule R (Lsum c))
    (eW : W ≃ₗ[R] DirectSum κ Lsum)
    {T : Type*} [AddCommGroup T] [Module R T] [IsSimpleModule R T]
    (incl : T →ₗ[R] W) (hincl : Function.Injective incl) :
    ∃ c, Nonempty (T ≃ₗ[R] Lsum c) := by
  classical
  set f : T →ₗ[R] DirectSum κ Lsum := eW.toLinearMap ∘ₗ incl with hf
  have hfinj : Function.Injective f := eW.injective.comp hincl
  set T' : Submodule R (DirectSum κ Lsum) := LinearMap.range f with hT'
  have eTT' : T ≃ₗ[R] T' := LinearEquiv.ofInjective f hfinj
  haveI : IsSimpleModule R T' := (LinearEquiv.isSimpleModule_iff eTT').mp ‹_›
  set cs : Set (Submodule R (DirectSum κ Lsum)) :=
    Set.range (fun c => LinearMap.range (DirectSum.lof R κ Lsum c)) with hcs
  have hlof_inj : ∀ c, Function.Injective (DirectSum.lof R κ Lsum c) := fun c =>
    Function.LeftInverse.injective (g := DirectSum.component R κ Lsum c)
      (fun b => DirectSum.component.lof_self R c b)
  have hcs_simple : ∀ m : cs, IsSimpleModule R (m : Submodule R (DirectSum κ Lsum)) := by
    rintro ⟨m, c, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hlof_inj c)).symm
  haveI := hcs_simple
  have hcs_top : sSup cs = ⊤ := by
    rw [hcs, sSup_range]; exact DFinsupp.iSup_range_lsingle
  have hTle : T' ≤ sSup cs := by rw [hcs_top]; exact le_top
  obtain ⟨m, hm, ⟨e'⟩⟩ := T'.linearEquiv_of_le_sSup cs hTle
  obtain ⟨c, rfl⟩ := hm
  exact ⟨c, ⟨eTT'.trans (e'.trans (LinearEquiv.ofInjective _ (hlof_inj c)).symm)⟩⟩

/-- An equivariant decomposition into simple summands admits an injective assignment from the
displayed index type to summands with the displayed auxiliary values. -/
theorem exists_injective_auxiliarySummandIndexing
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)) :
    ∃ φ : FinPartition N n → ι,
      Function.Injective φ ∧
      ∀ lam : FinPartition N n,
        weightCharacter k N (L (φ lam)) = partitionPolynomial N lam.parts := by
  classical
  have hmatch : ∀ lam : FinPartition N n,
      ∃ i : ι, weightCharacter k N (L i) = partitionPolynomial N lam.parts := by
    rintro ⟨parts, hdecr, hsum⟩
    subst hsum
    have hinter : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
        (x : schurSubmodule k N parts),
        (schurSubmodule k N parts).subtype (schurSubmoduleRepresentation k N parts g x)
          = tensorPowerRepresentation k N (∑ i, parts i) g
              ((schurSubmodule k N parts).subtype x) := by
      intro g x
      rfl
    letI : AddCommGroup (schurSubmodule k N parts) :=
      { Module.addCommMonoidToAddCommGroup k with
        toAddCommMonoid := (schurSubmodule k N parts).addCommMonoid }
    haveI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (schurSubmoduleRepresentation k N parts)) :=
      isSimpleModule_fdRep_of_antitone k N parts hdecr
    let incl : Representation.asModule (schurSubmoduleRepresentation k N parts) →ₗ[
        MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (tensorPowerRepresentation k N (∑ i, parts i)) :=
      linearMapAsModule (schurSubmodule k N parts).subtype hinter
    have hincl : Function.Injective incl := by
      intro a b hab
      apply Subtype.ext
      exact hab
    obtain ⟨ν, ⟨Φ⟩⟩ := simpleModule_linearEquiv_directSummand
      (W := Representation.asModule (tensorPowerRepresentation k N (∑ i, parts i)))
      (T := Representation.asModule (schurSubmoduleRepresentation k N parts))
      (Lsum := fun ν : Σ i : ι, Fin (Module.finrank k (S i)) =>
        Representation.asModule (L ν.1).ρ)
      (fun ν => hLsimp ν.1)
      (auxiliaryDefinition k N (∑ i, parts i) L e he)
      incl hincl
    refine ⟨ν.1, ?_⟩
    have hchar := auxiliaryValue_eq_of_linearEquiv k N
      (schurSubmoduleRepresentation k N parts) (L ν.1).ρ Φ
    have hbridge : weightCharacter k N (FDRep.of (L ν.1).ρ) = weightCharacter k N (L ν.1) := rfl
    have hschur : weightCharacter k N (FDRep.of (schurSubmoduleRepresentation k N parts))
        = partitionPolynomial N parts := schurRepresentation_weightCharacter k N parts hdecr
    rw [hbridge, hschur] at hchar
    exact hchar.symm
  choose φ hφ using hmatch
  refine ⟨φ, ?_, hφ⟩
  intro lam lam' heq
  have h1 : partitionPolynomial N lam.parts = partitionPolynomial N lam'.parts := by
    rw [← hφ lam, ← hφ lam', heq]
  have h2 : lam.parts = lam'.parts :=
    antitone_eq_of_auxiliaryPolynomial_eq N _ _ lam.parts_antitone lam'.parts_antitone h1
  obtain ⟨p, d, s⟩ := lam
  obtain ⟨p', d', s'⟩ := lam'
  obtain rfl : p = p' := h2
  rfl

/-- The displayed auxiliary values of pairwise nonisomorphic simple summands are linearly
independent under the stated hypotheses. -/
theorem linearIndependent_auxiliaryValues_of_pairwise_nonisomorphic
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (_he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLtop : ∀ i, ⨆ (μ : Fin N →₀ ℕ), weightSpace k N (L i) (fun j => μ j) = ⊤)
    (hLalg : ∀ i, HasAuxiliaryMapProperty N (L i).ρ)
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j)))) :
    LinearIndependent ℚ (fun i => weightCharacter k N (L i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have htorus : ∀ t : Fin N → kˣ,
      ∑ i, (c i : k) • LinearMap.trace k (L i) ((L i).ρ (unitTupleElement k N t)) = 0 := by
    intro t
    have h := sum_trace_unitTupleAction_eq_zero_of_auxiliaryPolynomialRelation
      k N Finset.univ c L (fun i _ => hLtop i) (by simpa using hc) t
    simpa using h
  exact trace_coefficients_eq_zero_of_diagonal_sum_eq_zero
    k N L hLalg hLsimp hLdist c htorus

private theorem auxiliaryWeightSpace_map_le_of_equivariant
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (W : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (f : V →ₗ[k] (W : Type))
    (hf : ∀ g v, f (ρV g v) = W.ρ g (f v)) (μ : Fin N → ℕ) :
    (weightSpace k N (FDRep.of ρV) μ).map f ≤ weightSpace k N W μ := by
  intro w hw
  rw [Submodule.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  simp only [weightSpace, Submodule.mem_iInf, LinearMap.mem_ker, FDRep.of_ρ',
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  intro a t
  have hvit : ρV (diagonalUnit k N a t) v = (↑t : k) ^ μ a • v := sub_eq_zero.mp (hv a t)
  have hwit : W.ρ (diagonalUnit k N a t) (f v) = (↑t : k) ^ μ a • f v := by
    rw [← hf, hvit, map_smul]
  rw [sub_eq_zero]; exact hwit

/-- Every positive-multiplicity summand in the equivariant direct-sum decomposition has the
displayed auxiliary supremum equal to top. -/
theorem summand_auxiliarySup_eq_top
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hSne : ∀ i, 0 < Module.finrank k (S i)) :
    ∀ i, ⨆ (μ : Fin N →₀ ℕ), weightSpace k N (L i) (fun j => μ j) = ⊤ := by
  classical
  intro i
  let b : Module.Basis (Fin (Module.finrank k (S i))) k (S i) := Module.finBasis k (S i)
  let i0 : Fin (Module.finrank k (S i)) := ⟨0, hSne i⟩
  let φ : (S i) →ₗ[k] k := b.coord i0
  have hφ : φ (b i0) = 1 := by
    change b.coord i0 (b i0) = 1
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  let r : (S i ⊗[k] (L i : Type)) →ₗ[k] (L i : Type) :=
    (TensorProduct.lid k (L i : Type)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hr_tmul : ∀ (a : S i) (x : (L i : Type)), r (a ⊗ₜ x) = φ a • x := by
    intro a x
    simp [r, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  have hr_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (y : S i ⊗[k] (L i : Type)),
      r (((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
            (L i).ρ) g y) = (L i).ρ g (r y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        simp only [Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.trivial_apply, hr_tmul, map_smul]
    | add y z hy hz => simp only [map_add, hy, hz]
  let q : auxiliarySpace k (Fin N → k) n →ₗ[k] (L i : Type) :=
    r ∘ₗ (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i) ∘ₗ (e.toLinearMap)
  have coord : ∀ (x : DirectSum ι (fun j => S j ⊗[k] (L j : Type)))
      (g : Matrix.GeneralLinearGroup (Fin N) k),
      DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i
          (Representation.directSum (fun j =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (S j)).tprod (L j).ρ) g x)
        = ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
            (L i).ρ) g
            (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i x) := by
    intro x g
    change (DirectSum.lmap (fun m =>
      ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S m)).tprod
        (L m).ρ) g) x) i
      = ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
          (L i).ρ) g (x i)
    rw [DirectSum.lmap_apply]
  have hq : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
      (v : auxiliarySpace k (Fin N → k) n),
      q (tensorPowerRepresentation k N n g v) = (L i).ρ g (q v) := by
    intro g v
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [he, coord, hr_equiv]
  have hsurj : Function.Surjective q := by
    intro x
    refine ⟨e.symm
      (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type)) i (b i0 ⊗ₜ x)), ?_⟩
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]
    rw [hr_tmul, hφ, one_smul]
  have hmap_top : Submodule.map q ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  refine le_antisymm le_top ?_
  calc (⊤ : Submodule k (L i : Type))
      = Submodule.map q ⊤ := hmap_top.symm
    _ = Submodule.map q (⨆ μ : Fin N →₀ ℕ,
          weightSpace k N (FDRep.of (tensorPowerRepresentation k N n)) (fun j => μ j)) := by
          rw [auxiliaryRepresentation_iSupWeightSpace_eq_top]
    _ = ⨆ μ : Fin N →₀ ℕ, Submodule.map q
          (weightSpace k N (FDRep.of (tensorPowerRepresentation k N n)) (fun j => μ j)) :=
          Submodule.map_iSup _ _
    _ ≤ ⨆ μ : Fin N →₀ ℕ, weightSpace k N (L i) (fun j => μ j) :=
          iSup_mono fun μ =>
            auxiliaryWeightSpace_map_le_of_equivariant N
              (tensorPowerRepresentation k N n) (L i) q hq (fun j => μ j)

private theorem hasAuxiliaryMapProperty_of_equivariant_linearEquiv
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}
    {Y Y' : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [AddCommGroup Y'] [Module k Y'] [Module.Finite k Y']
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    {ρ' : Matrix.GeneralLinearGroup (Fin N) k → Y' →ₗ[k] Y'}
    (φ : Y ≃ₗ[k] Y')
    (hφ : ∀ g y, φ (ρ g y) = ρ' g (φ y))
    (h : HasAuxiliaryMapProperty N ρ) :
    HasAuxiliaryMapProperty N ρ' := by
  obtain ⟨m, b, P, hP⟩ := h
  refine ⟨m, b.map φ, P, fun g a c => ?_⟩
  have h2 : (b.map φ).repr (φ (ρ g (b c))) = b.repr (ρ g (b c)) := by
    change (φ.symm.trans b.repr) (φ (ρ g (b c))) = b.repr (ρ g (b c))
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change (b.map φ).repr (ρ' g ((b.map φ) c)) a =
    auxiliaryPolynomialEvaluation g (P a c)
  rw [show ((b.map φ) c) = φ (b c) from rfl, ← hφ, h2, hP g a c]

/-- Every positive-multiplicity summand in the equivariant direct-sum decomposition satisfies
the specified auxiliary predicate. -/
theorem summand_auxiliaryProperty
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hSne : ∀ i, 0 < Module.finrank k (S i)) :
    ∀ i, HasAuxiliaryMapProperty N (L i).ρ := by
  classical
  intro i
  let bS : Module.Basis (Fin (Module.finrank k (S i))) k (S i) := Module.finBasis k (S i)
  let i0 : Fin (Module.finrank k (S i)) := ⟨0, hSne i⟩
  let φ : (S i) →ₗ[k] k := bS.coord i0
  have hφ1 : φ (bS i0) = 1 := by
    change bS.coord i0 (bS i0) = 1
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  let s : (L i : Type) →ₗ[k] auxiliarySpace k (Fin N → k) n :=
    e.symm.toLinearMap ∘ₗ
      (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type)) i) ∘ₗ
      (TensorProduct.mk k (S i) (L i : Type) (bS i0))
  have hs_apply : ∀ x : (L i : Type),
      s x = e.symm (DirectSum.lof k ι (fun j => S j ⊗[k] (L j : Type)) i (bS i0 ⊗ₜ x)) :=
    fun _ => rfl
  have hs_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : (L i : Type)),
      tensorPowerRepresentation k N n g (s x) = s ((L i).ρ g x) := by
    intro g x
    apply e.injective
    rw [he, hs_apply, hs_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      Representation.directSum_apply, DirectSum.lmap_lof, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.trivial_apply]
  let r : (S i ⊗[k] (L i : Type)) →ₗ[k] (L i : Type) :=
    (TensorProduct.lid k (L i : Type)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hr_tmul : ∀ (a : S i) (x : (L i : Type)), r (a ⊗ₜ x) = φ a • x := by
    intro a x; simp [r, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  let q : auxiliarySpace k (Fin N → k) n →ₗ[k] (L i : Type) :=
    r ∘ₗ (DirectSum.component k ι (fun j => S j ⊗[k] (L j : Type)) i) ∘ₗ (e.toLinearMap)
  have hqs : ∀ x : (L i : Type), q (s x) = x := by
    intro x
    simp only [q, s, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, DirectSum.component.lof_self, TensorProduct.mk_apply]
    rw [hr_tmul, hφ1, one_smul]
  have hs_inj : Function.Injective s := Function.LeftInverse.injective hqs
  set W : Submodule k (auxiliarySpace k (Fin N → k) n) := LinearMap.range s with hW
  have hWinv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
      ∀ v ∈ W, tensorPowerRepresentation k N n g v ∈ W := by
    intro g v hv
    obtain ⟨x, rfl⟩ := hv
    exact ⟨(L i).ρ g x, (hs_equiv g x).symm⟩
  have hWalg :=
    (auxiliaryRepresentation_property k N n).auxiliary_restrict W hWinv
  let φW : (L i : Type) ≃ₗ[k] W := LinearEquiv.ofInjective s hs_inj
  have hφWval : ∀ y : (L i : Type), (φW y : auxiliarySpace k (Fin N → k) n) = s y :=
    fun _ => rfl
  refine hasAuxiliaryMapProperty_of_equivariant_linearEquiv φW.symm ?_ hWalg
  intro g w
  apply φW.injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearMap.coe_restrict_apply, hφWval, ← hs_equiv, ← hφWval,
    LinearEquiv.apply_symm_apply]

/-- Pairwise nonisomorphic simple summands of the decomposition admit an injective labeling
whose labels give their displayed auxiliary values. -/
theorem exists_injective_auxiliaryLabeling
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module.Finite k (S i)]
    (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
    (he : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v))
    (hLsimp : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
    (hLdist : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
    (hSne : ∀ i, 0 < Module.finrank k (S i)) :
    ∃ lam : ι → {l : Fin N → ℕ // Antitone l},
      Function.Injective lam ∧
      ∀ i, weightCharacter k N (L i) = partitionPolynomial N (lam i).val := by
  have hBP : ∀ {a b : FinPartition N n}, a.parts = b.parts → a = b := by
    rintro ⟨p, d, s⟩ ⟨p', d', s'⟩ h
    obtain rfl : p = p' := h
    rfl
  obtain ⟨φ, hφinj, hφchar⟩ :=
    exists_injective_auxiliarySummandIndexing k N n L e he hLsimp
  have hφsurj : Function.Surjective φ := by
    have hLtop : ∀ i, ⨆ (μ : Fin N →₀ ℕ),
        weightSpace k N (L i) (fun j => μ j) = ⊤ :=
      summand_auxiliarySup_eq_top k N n L e he hSne
    have hLalg : ∀ i, HasAuxiliaryMapProperty N (L i).ρ :=
      summand_auxiliaryProperty k N n L e he hSne
    have hLI := linearIndependent_auxiliaryValues_of_pairwise_nonisomorphic
      k N n L e he hLtop hLalg hLsimp hLdist
    have hnum := weightedAuxiliaryValue_sum_eq k N n L e he
    set v : ι → MvPolynomial (Fin N) ℚ := fun i => weightCharacter k N (L i) with hvdef
    obtain ⟨mfun, hmeq⟩ : ∃ mfun : FinPartition N n → ℚ,
        ∑ i, (Module.finrank k (S i) : ℚ) • v i
          = ∑ lam : FinPartition N n, mfun lam • partitionPolynomial N lam.parts :=
      ⟨_, hnum⟩
    have hfib : ∑ i : ι,
          (∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i), mfun lam) • v i
        = ∑ lam : FinPartition N n, mfun lam • partitionPolynomial N lam.parts := by
      rw [← Finset.sum_fiberwise Finset.univ φ
        (fun lam => mfun lam • partitionPolynomial N lam.parts)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun lam hlam => ?_
      have hli : φ lam = i := (Finset.mem_filter.mp hlam).2
      rw [← hli]
      simp only [hvdef]
      rw [hφchar lam]
    have hkey : ∑ i, ((Module.finrank k (S i) : ℚ)
        - ∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i), mfun lam) • v i = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib, hfib, ← hmeq, sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hLI)
      (fun i => (Module.finrank k (S i) : ℚ)
        - ∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i), mfun lam) hkey
    intro i₀
    by_contra hni
    have hempty : Finset.univ.filter (fun lam => φ lam = i₀)
        = (∅ : Finset (FinPartition N n)) := by
      rw [Finset.filter_eq_empty_iff]
      intro lam _ h
      exact hni ⟨lam, h⟩
    have hd0 : (Module.finrank k (S i₀) : ℚ)
        - ∑ lam ∈ Finset.univ.filter (fun lam => φ lam = i₀), mfun lam = 0 := hcoeff i₀
    rw [hempty, Finset.sum_empty, sub_zero] at hd0
    have hz : Module.finrank k (S i₀) = 0 := by exact_mod_cast hd0
    exact (hSne i₀).ne' hz
  let φequiv : FinPartition N n ≃ ι := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  refine ⟨fun i => ⟨(φequiv.symm i).parts, (φequiv.symm i).parts_antitone⟩, ?_, ?_⟩
  · intro i j hij
    exact φequiv.symm.injective (hBP (congrArg Subtype.val hij))
  · intro i
    have hi : L (φ (φequiv.symm i)) = L i := congrArg L (φequiv.apply_symm_apply i)
    rw [← hi]
    exact hφchar (φequiv.symm i)

/-- Under the stated hypotheses, a simple representation is isomorphic to the displayed
auxiliary representation when their auxiliary values agree. -/
theorem iso_auxiliaryRepresentation_of_auxiliaryValue_eq (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (hLtop : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N L (fun i => μ i) = ⊤)
    (hLalg : HasAuxiliaryMapProperty N L.ρ)
    (h : weightCharacter k N L = partitionPolynomial N lam) :
    Nonempty (L ≅ schurRepresentation k N lam) := by
  by_contra hno
  let S := schurRepresentation k N lam
  have hSchar : weightCharacter k N S = partitionPolynomial N lam :=
    schurRepresentation_weightCharacter k N lam hlam
  have hSsimp : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule S.ρ) := isSimpleModule_fdRep_of_antitone k N lam hlam
  have htop : ∀ i, ⨆ (μ : Fin N →₀ ℕ),
      weightSpace k N (![L, S] i) (fun j => μ j) = ⊤ := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · change (⨆ (μ : Fin N →₀ ℕ), weightSpace k N L (fun j => μ j)) = ⊤
      exact hLtop
    · change (⨆ (μ : Fin N →₀ ℕ),
        weightSpace k N (schurRepresentation k N lam) (fun j => μ j)) = ⊤
      exact auxiliarySup_eq_top_for_auxiliaryRepresentation k N lam
  have hsimp : ∀ i, IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (![L, S] i).ρ) := by
    rw [Fin.forall_fin_two]; exact ⟨hLsimp, hSsimp⟩
  have hSalg : HasAuxiliaryMapProperty N S.ρ := by
    exact auxiliaryFDRep_property N lam
  have halg : ∀ i, HasAuxiliaryMapProperty N (![L, S] i).ρ := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · change HasAuxiliaryMapProperty N L.ρ
      exact hLalg
    · change HasAuxiliaryMapProperty N S.ρ
      exact hSalg
  have hdist : Pairwise (fun i j => ¬ Nonempty ((![L, S] i) ≅ (![L, S] j))) := by
    have hsym : ¬ Nonempty (S ≅ L) := fun ⟨e⟩ => hno ⟨e.symm⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simpa using hno
        | simpa using hsym
  have hcharsum : ∑ i, (![(1 : ℚ), -1] i) • weightCharacter k N (![L, S] i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h, hSchar, one_smul, neg_one_smul, add_neg_cancel]
  have htorus : ∀ t : Fin N → kˣ,
      ∑ i, ((![(1 : ℚ), -1] i : ℚ) : k) •
        LinearMap.trace k (![L, S] i) ((![L, S] i).ρ (unitTupleElement k N t)) = 0 := by
    intro t
    exact sum_trace_unitTupleAction_eq_zero_of_auxiliaryPolynomialRelation k N Finset.univ
      ![(1 : ℚ), -1] ![L, S] (fun i _ => htop i) hcharsum t
  have hzero := trace_coefficients_eq_zero_of_diagonal_sum_eq_zero
    k N ![L, S] halg hsimp hdist ![(1 : ℚ), -1] htorus
  simpa using hzero 0

/-- Under the stated hypotheses, a representation is isomorphic to the displayed auxiliary
representation when their auxiliary values and dimensions agree. -/
theorem iso_of_auxiliaryConditions_and_finrank_eq (N : ℕ)
    (lam : Fin N → ℕ) (hlam : Antitone lam)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h : weightCharacter k N M = partitionPolynomial N lam)
    (_h_dim : Module.finrank k M = Module.finrank k (schurRepresentation k N lam)) :
    Nonempty (M ≅ schurRepresentation k N lam) := by
  classical
  set n := ∑ i, lam i with hn
  have h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n := by
    intro μ hμ
    have hpos : 0 < Module.finrank k (weightSpace k N M μ) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hμ)
    exact auxiliaryWeight_degree_eq_of_polynomial_eq k N lam M h μ hpos
  obtain ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, hLdist, hSne, e, he,
      p, f, ⟨eM⟩⟩ :=
    existsLinearEquivFiniteDirectSum k N n M halg h_span h_homog
  letI := hιFin; letI := hιDec
  letI : ∀ i, AddCommGroup (S i) := hSacg
  letI : ∀ i, Module k (S i) := hSmod
  letI : ∀ i, Module.Finite k (S i) := hSfin
  obtain ⟨lam_cl, lam_inj, hchar⟩ :=
    exists_injective_auxiliaryLabeling k N n L e he hLsimp hLdist hSne
  have hφ : Representation.asModule M.ρ ≃ₗ[MonoidAlgebra k
      (Matrix.GeneralLinearGroup (Fin N) k)]
      Representation.asModule (Representation.directSum (fun j : Fin p => (L (f j)).ρ)) :=
    eM ≪≫ₗ (directSumAsModuleEquiv (fun j : Fin p => (L (f j)).ρ)).symm
  have hM_sum : weightCharacter k N M =
      ∑ j : Fin p, partitionPolynomial N (lam_cl (f j)).val := by
    have hchar_eq : weightCharacter k N M
        = weightCharacter k N
          (FDRep.of (Representation.directSum (fun j : Fin p => (L (f j)).ρ))) := by
      have h0 := auxiliaryPolynomial_eq_of_linearEquiv k N M.ρ
        (Representation.directSum (fun j : Fin p => (L (f j)).ρ))
        (representationLinearEquiv hφ)
        (fun g v => representationLinearEquiv_intertwines hφ g v)
      rwa [auxiliary_fdRep_value_of_representation_eq] at h0
    rw [hchar_eq,
      auxiliaryPolynomial_directSum k N (fun j : Fin p => (L (f j) : Type))
        (fun j : Fin p => (L (f j)).ρ)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [auxiliary_fdRep_value_of_representation_eq, hchar (f j)]
  have hrel : partitionPolynomial N lam =
      ∑ j : Fin p, partitionPolynomial N (lam_cl (f j)).val := by
    rw [← h, hM_sum]
  have hsum_eq : Finsupp.single (⟨lam, hlam⟩ : {l : Fin N → ℕ // Antitone l}) (1 : ℚ)
      = ∑ j : Fin p, Finsupp.single (lam_cl (f j)) (1 : ℚ) := by
    apply auxiliaryPolynomial_linearIndependent N
    rw [Finsupp.linearCombination_single, map_sum]
    simp only [Finsupp.linearCombination_single, one_smul]
    exact hrel
  have hp1 : p = 1 := by
    have hmass := congrArg
      (Finsupp.linearCombination ℚ
        (fun _ : {l : Fin N → ℕ // Antitone l} => (1 : ℚ))) hsum_eq
    simp only [map_sum, Finsupp.linearCombination_single, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmass
    exact_mod_cast hmass.symm
  subst hp1
  have hclass0 : lam_cl (f 0) = (⟨lam, hlam⟩ : {l : Fin N → ℕ // Antitone l}) := by
    rw [Fin.sum_univ_one] at hsum_eq
    exact (Finsupp.single_left_inj (by norm_num)).mp hsum_eq.symm
  let e_collapse :
      DirectSum (Fin 1) (fun j : Fin 1 => Representation.asModule (L (f j)).ρ)
        ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
          Representation.asModule (L (f 0)).ρ :=
    LinearEquiv.ofLinear
      (DirectSum.component (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) (Fin 1)
        (fun j : Fin 1 => Representation.asModule (L (f j)).ρ) 0)
      (DirectSum.lof (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) (Fin 1)
        (fun j : Fin 1 => Representation.asModule (L (f j)).ρ) 0)
      (by ext x; simp )
      (by
        refine DirectSum.linearMap_ext
          (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) (fun i => ?_)
        fin_cases i
        ext b j
        fin_cases j
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        congr)
  have hφ' : Representation.asModule M.ρ
      ≃ₗ[MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)]
        Representation.asModule (L (f 0)).ρ :=
    eM ≪≫ₗ e_collapse
  have hML : Nonempty (M ≅ L (f 0)) :=
    ⟨Action.mkIso (representationLinearEquiv hφ').toFGModuleCatIso (fun g => by
      ext x
      exact representationLinearEquiv_intertwines hφ' g x)⟩
  have hchar0 : weightCharacter k N (L (f 0)) = partitionPolynomial N lam := by
    rw [hchar (f 0), hclass0]
  have hLf0top : ⨆ (μ : Fin N →₀ ℕ),
      weightSpace k N (L (f 0)) (fun i => μ i) = ⊤ :=
    auxiliarySup_eq_top_of_surjective_equivariant k N M (L (f 0))
      (representationLinearEquiv hφ').toLinearMap
      (fun g v => representationLinearEquiv_intertwines hφ' g v)
      (representationLinearEquiv hφ').surjective h_span
  have hLf0alg : HasAuxiliaryMapProperty N (L (f 0)).ρ :=
    HasAuxiliaryMapProperty.auxiliary_of_linearEquiv
      (representationLinearEquiv hφ')
      (fun g v => representationLinearEquiv_intertwines hφ' g v) halg
  have hLS : Nonempty (L (f 0) ≅ schurRepresentation k N lam) :=
    iso_auxiliaryRepresentation_of_auxiliaryValue_eq k N lam hlam (L (f 0)) (hLsimp (f 0))
      hLf0top hLf0alg hchar0
  obtain ⟨isoML⟩ := hML
  obtain ⟨isoLS⟩ := hLS
  exact ⟨isoML ≪≫ isoLS⟩

end

end RepresentationTheory.GeneralLinear.AuxiliaryDecomposition

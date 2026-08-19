/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.AuxiliaryCharacter
import RepresentationTheory.PolynomialMatrixCoefficients
import RepresentationTheory.AsModuleEquivalences
import RepresentationTheory.TensorPower
import RepresentationTheory.LinearAlgebra.EndomorphismCentralizer
import RepresentationTheory.Auxiliary.LinearIndependence
import RepresentationTheory.Algebra.Module.Simple

set_option linter.dupNamespace false

namespace RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition

open scoped TensorProduct DirectSum
open CategoryTheory
open RepresentationTheory.Algebra.Module.Simple
open RepresentationTheory.AsModuleEquivalences
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.GeneralLinearGroup.Auxiliary
open RepresentationTheory.GeneralLinearGroup.WeightCharacter
open RepresentationTheory.LinearAlgebra.EndomorphismCentralizer
open RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary
open RepresentationTheory.TensorPower

variable (k : Type) [Field k] (N : ℕ)

/-- An auxiliary type family indexed by a field and a natural number. -/
abbrev auxiliaryFieldNatType := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)

set_option maxHeartbeats 3200000 in
-- Increased for the combined tensor-decomposition and instance-synthesis argument.
set_option synthInstance.maxHeartbeats 1600000 in

/-- For an algebraically closed field of characteristic zero, asserts the existence of
displayed data including a map that intertwines a general linear group action with a direct
sum of tensor products involving trivial representations. -/
theorem existsActionIntertwiningData
    [IsAlgClosed k] [CharZero k] (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (auxiliaryFieldNatType k N) (Representation.asModule (L i).ρ))
      (_ : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
      (_ : ∀ i, 0 < Module.finrank k (S i)),
      ∃ (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
          (DirectSum ι (fun i => S i ⊗[k] (L i : Type)))),
        ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : auxiliarySpace k (Fin N → k) n),
          e (tensorPowerRepresentation k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v) := by
  classical
  letI : Ring (permutationActionAlgebra k (Fin N → k) n) :=
    @Subalgebra.toRing k
    (Module.End k (auxiliarySpace k (Fin N → k) n)) inferInstance inferInstance
    inferInstance (permutationActionAlgebra k (Fin N → k) n)
  obtain ⟨ι, hιFin, hιDec, S', hS'_simp, hS'_dist, hSi_fin, L, hL_simple,
      L_carrier, e, he, h_act⟩ :=
    exists_tensorProduct_decomposition_with_action k N n
  let coherentSAddCommGroup : ∀ i, AddCommGroup (S' i) := fun i =>
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (S' i).addCommMonoid }
  letI : ∀ i, AddCommGroup (S' i) := coherentSAddCommGroup
  refine ⟨ι, hιFin, hιDec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance,
    fun i => hSi_fin i, L, hL_simple,
    pairwise_not_iso_of_submodule_equiv N n S' hS'_simp hS'_dist L L_carrier h_act,
    (fun i => by
      haveI : IsSimpleModule (permutationActionAlgebra k (Fin N → k) n) (S' i) :=
        hS'_simp i
      haveI := hSi_fin i
      haveI : Nontrivial (↥(S' i)) :=
        IsSimpleModule.nontrivial (permutationActionAlgebra k (Fin N → k) n) (↥(S' i))
      exact Module.finrank_pos),
    ?_, ?_⟩
  · exact e
  intro g v
  have h_lin :
      (tensorPowerRepresentation k N n g) ∘ₗ (e.symm : _ →ₗ[k] _) =
        (e.symm : _ →ₗ[k] _) ∘ₗ
          (Representation.directSum (fun i =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (↥(S' i))).tprod (L i).ρ) g) := by
    refine DirectSum.linearMap_ext k fun i => ?_
    apply TensorProduct.ext'
    intro s l
    change (tensorPowerRepresentation k N n g) (e.symm
        (DirectSum.lof k ι (fun i => ↥(S' i) ⊗[k] (L i : Type)) i
          (s ⊗ₜ[k] l))) =
      e.symm ((Representation.directSum (fun i =>
        (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
          (↥(S' i))).tprod (L i).ρ) g)
        (DirectSum.lof k ι _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lof_eq_of, he i s l]
    change _ = e.symm (DirectSum.lmap
      (fun i => ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (DirectSum.of _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lmap_of, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, he i s ((L i).ρ g l)]
    exact (h_act i g l s).symm
  have h := LinearMap.congr_fun h_lin (e v)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [show (e.symm : _ →ₗ[k] _) (e v) = v from e.symm_apply_apply v] at h
  rw [show (e.symm : _ →ₗ[k] _) ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) =
    e.symm ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) from rfl] at h
  exact (LinearEquiv.eq_symm_apply e).mp h

/-- Under the displayed hypotheses on a finite-dimensional representation, asserts an
existential statement whose terminal predicate is elided. -/
theorem existsElidedData
    [IsAlgClosed k] [CharZero k] (n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type) (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (auxiliaryFieldNatType k N) (Representation.asModule (L i).ρ))
      (_ : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
      (_ : ∀ i, 0 < Module.finrank k (S i))
      (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
          (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
      (_ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
            (v : auxiliarySpace k (Fin N → k) n),
            e (tensorPowerRepresentation k N n g v) =
              Representation.directSum (fun i =>
                (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                  (S i)).tprod (L i).ρ) g (e v))
      (κ : Type) (_ : Finite κ) (gκ : κ → ι)
      (W : Type) (_ : AddCommGroup W) (_ : Module (auxiliaryFieldNatType k N) W)
      (_ : W ≃ₗ[auxiliaryFieldNatType k N]
        DirectSum κ (fun c => Representation.asModule (L (gκ c)).ρ))
      (M' : Submodule (auxiliaryFieldNatType k N) W),
      Nonempty (Representation.asModule M.ρ ≃ₗ[auxiliaryFieldNatType k N] M') := by
  classical
  obtain ⟨m, φ, hφinj, hφeq⟩ :=
    exists_injective_equivariant_tensorFamilyMap_of_auxiliarySubmodules
      (M := M) (halg := halg) (h_span := h_span) (h_homog := h_homog)
  obtain ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, hLdist, hSne, e, he⟩ :=
    existsActionIntertwiningData (k := k) (N := N) n
  haveI iSfree : ∀ i, Module.Free k (S i) := fun i => Module.Free.of_divisionRing k (S i)
  set β : ι → Type := fun i => Fin (Module.finrank k (S i)) with hβ
  set piToDS := (DirectSum.linearEquivFunOnFintype k (Fin m)
    (fun _ : Fin m => auxiliarySpace k (Fin N → k) n)).symm with hpiToDS
  set φ' : (M : Type) →ₗ[k]
      DirectSum (Fin m) (fun _ : Fin m => auxiliarySpace k (Fin N → k) n) :=
    piToDS.toLinearMap ∘ₗ φ with hφ'
  have hφ'inj : Function.Injective φ' := piToDS.injective.comp hφinj
  have hcoe : ∀ (w : Fin m → auxiliarySpace k (Fin N → k) n) (a : Fin m),
      (piToDS w) a = w a := by intro w a; rw [hpiToDS]; rfl
  have hφ'eq : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : (M : Type)),
      φ' (M.ρ g x) =
        Representation.directSum (fun _ : Fin m => tensorPowerRepresentation k N n) g (φ' x) := by
    intro g x
    refine DFinsupp.ext fun a => ?_
    rw [show φ' (M.ρ g x) = piToDS (φ (M.ρ g x)) from rfl,
        show φ' x = piToDS (φ x) from rfl, hcoe,
        Representation.directSum_apply, DirectSum.lmap_apply, hcoe, hφeq]
    simp only [Matrix.toLin'_apply']
    rfl
  let φR : Representation.asModule M.ρ →ₗ[auxiliaryFieldNatType k N]
      Representation.asModule
        (Representation.directSum (fun _ : Fin m => tensorPowerRepresentation k N n)) :=
    linearMapAsModule φ' hφ'eq
  have hφRinj : Function.Injective φR := hφ'inj
  let Einner :
      Representation.asModule (tensorPowerRepresentation k N n) ≃ₗ[auxiliaryFieldNatType k N]
        DirectSum (Σ i : ι, β i) (fun ν => Representation.asModule (L ν.1).ρ) :=
    (linearEquivAsModule e he) ≪≫ₗ
      (directSumAsModuleEquiv (fun i =>
        (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod
          (L i).ρ)) ≪≫ₗ
      (DFinsupp.mapRange.linearEquiv (fun i =>
        trivialTensorAsModuleEquiv (Module.finBasis k (S i)) (L i).ρ)) ≪≫ₗ
      (DirectSum.sigmaLcurryEquiv (R := auxiliaryFieldNatType k N)
        (δ := fun (i : ι) (_ : β i) => Representation.asModule (L i).ρ)).symm
  let E1 := directSumAsModuleEquiv (fun _ : Fin m => tensorPowerRepresentation k N n)
  let E2 := DFinsupp.mapRange.linearEquiv (fun _ : Fin m => Einner)
  let Eouter := (DirectSum.sigmaLcurryEquiv (R := auxiliaryFieldNatType k N)
    (δ := fun (_ : Fin m) (ν : Σ i : ι, β i) => Representation.asModule (L ν.1).ρ)).symm
  let ψ := (Eouter.toLinearMap ∘ₗ E2.toLinearMap ∘ₗ E1.toLinearMap) ∘ₗ φR
  have hψinj : Function.Injective ψ :=
    ((Eouter.injective.comp E2.injective).comp E1.injective).comp hφRinj
  refine ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, hLdist, hSne, e, he,
    (Σ _ : Fin m, Σ i : ι, β i), inferInstance, (fun c => c.2.1),
    DirectSum (Σ _ : Fin m, Σ i : ι, β i) (fun c => Representation.asModule (L c.2.1).ρ),
    inferInstance, inferInstance, LinearEquiv.refl (auxiliaryFieldNatType k N) _,
    LinearMap.range ψ, ⟨LinearEquiv.ofInjective ψ hψinj⟩⟩

/-- Under the displayed hypotheses on a finite-dimensional representation, asserts the
existence of auxiliary data including a nonempty linear equivalence from its underlying
module to a finite direct sum of underlying modules of an existentially supplied family of
representations. -/
theorem existsLinearEquivFiniteDirectSum
    [IsAlgClosed k] [CharZero k] (n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type) (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (auxiliaryFieldNatType k N) (Representation.asModule (L i).ρ))
      (_ : Pairwise (fun i j => ¬ Nonempty ((L i) ≅ (L j))))
      (_ : ∀ i, 0 < Module.finrank k (S i))
      (e : auxiliarySpace k (Fin N → k) n ≃ₗ[k]
          (DirectSum ι (fun i => S i ⊗[k] (L i : Type))))
      (_ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
            (v : auxiliarySpace k (Fin N → k) n),
            e (tensorPowerRepresentation k N n g v) =
              Representation.directSum (fun i =>
                (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                  (S i)).tprod (L i).ρ) g (e v))
      (p : ℕ) (f : Fin p → ι),
      Nonempty (Representation.asModule M.ρ ≃ₗ[auxiliaryFieldNatType k N]
        DirectSum (Fin p) (fun j => Representation.asModule (L (f j)).ρ)) := by
  classical
  obtain ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, hLdist, hSne, e, he,
      κ, hκFin, gκ, W, hWacg, hWmod, eW, M', ⟨eM⟩⟩ :=
    existsElidedData k N n M halg h_span h_homog
  set Lsum : κ → Type := fun c => Representation.asModule (L (gκ c)).ρ with hLsum
  haveI : ∀ c, IsSimpleModule (auxiliaryFieldNatType k N) (Lsum c) := fun c => hLsimp (gκ c)
  obtain ⟨p, h, ⟨eM'⟩⟩ :=
    Submodule.nonempty_linearEquiv_directSumFin_of_simple
      (R := auxiliaryFieldNatType k N) Lsum (fun c => hLsimp (gκ c)) eW M'
  refine ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, hLdist, hSne, e, he,
    p, fun j => gκ (h j), ⟨?_⟩⟩
  exact eM.trans eM'

end RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition

/-- An auxiliary statement whose displayed formal type contains an elided term. -/
alias _root_.RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryElidedStatement006690 := _root_.RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.existsElidedData

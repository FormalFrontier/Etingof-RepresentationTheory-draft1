/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition
import RepresentationTheory.GeneralLinearGroup.DiagonalAction
import RepresentationTheory.Auxiliary.GeneralLinearGroupPolynomialEvaluation
import RepresentationTheory.AuxiliaryCharacter





















open CategoryTheory
open scoped TensorProduct DirectSum

noncomputable section

namespace RepresentationTheory.GeneralLinearGroup.AuxiliaryDecomposition

open RepresentationTheory RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition







/-- A family of submodules below an independent family equals that family when its supremum is top. -/
theorem Submodule.family_eq_of_le_iSupIndep_iSup_eq_top
    {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {ι : Type*} {T E : ι → Submodule R M}
    (hle : ∀ i, T i ≤ E i) (hE : iSupIndep E) (hT : ⨆ i, T i = ⊤) (i : ι) :
    T i = E i := by
  refine le_antisymm (hle i) ?_
  have hcover : E i ≤ T i ⊔ ⨆ (j) (_ : j ≠ i), E j := by
    calc E i ≤ ⊤ := le_top
      _ = ⨆ j, T j := hT.symm
      _ ≤ T i ⊔ ⨆ (j) (_ : j ≠ i), E j := by
          refine iSup_le (fun j => ?_)
          by_cases hj : j = i
          · subst hj; exact le_sup_left
          · exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj (hle j)))
  have hstep : E i = (T i ⊔ ⨆ (j) (_ : j ≠ i), E j) ⊓ E i := (inf_eq_right.mpr hcover).symm
  rw [hstep, sup_inf_assoc_of_le _ (hle i), inf_comm, (hE i).eq_bot, sup_bot_eq]

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)







/-- The representation module is semisimple under the displayed auxiliary property, spanning condition, and common index-sum condition. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.isSemisimpleModule_of_auxiliaryConditions (n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N) (Representation.asModule M.ρ) := by
  obtain ⟨ι, _, _, S, _, _, _, L, hLsimp, _, _, e, he, p, f, ⟨eM⟩⟩ :=
    RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.existsLinearEquivFiniteDirectSum k N n M halg h_span h_homog
  haveI : ∀ j : Fin p, IsSimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N) (Representation.asModule (L (f j)).ρ) :=
    fun j => hLsimp (f j)
  haveI : ∀ j : Fin p, IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N) (Representation.asModule (L (f j)).ρ) :=
    fun j => inferInstance
  haveI : IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N)
      (DirectSum (Fin p) (fun j => Representation.asModule (L (f j)).ρ)) :=
    inferInstanceAs (IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N)
      (Π₀ j : Fin p, Representation.asModule (L (f j)).ρ))
  exact IsSemisimpleModule.congr eM




/-- The distinguished auxiliary unit of the field. -/
def GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit : kˣ := Units.mk0 (2 : k) two_ne_zero

/-- The value of the auxiliary unit is equal to two. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit_val_eq_two : (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k : k) = 2 := rfl

/-- Taking natural powers of the auxiliary unit defines an injective map. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit_pow_injective : Function.Injective (fun d : ℕ => (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k : k) ^ d) := by
  intro a b hab
  simp only [GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit_val_eq_two] at hab
  have h : ((2 ^ a : ℕ) : k) = ((2 ^ b : ℕ) : k) := by push_cast; exact hab
  exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h)


/-- The displayed auxiliary general linear element commutes with every general linear group element. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryGeneralLinearElement_commutes (t : kˣ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N t * g = g * RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N t := by
  apply Units.ext
  change (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N t).val * (g : Matrix (Fin N) (Fin N) k)
      = (g : Matrix (Fin N) (Fin N) k) * (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N t).val
  have hval : (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N t).val = Matrix.scalar (Fin N) (t : k) := by
    rw [Matrix.scalar_apply]; rfl
  rw [hval]
  exact Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) (g : Matrix (Fin N) (Fin N) k)



/-- The displayed auxiliary general linear element is the ordered noncommutative product of its indexed factors. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryGeneralLinearElement_eq_noncommProd (t : kˣ) :
    RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N t
      = Finset.univ.noncommProd (fun i => RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t)
          (fun i _ j _ _ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit_comm k N i t j t) := by
  apply Units.ext
  have gen : ∀ (s : Finset (Fin N))
      (comm : (↑s : Set (Fin N)).Pairwise
        fun a b => Commute (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N a t) (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N b t)),
      (s.noncommProd (fun i => RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) comm).val
        = Matrix.diagonal (fun j => if j ∈ s then (t : k) else 1) := by
    intro s
    induction s using Finset.induction with
    | empty => intro comm; simp [Matrix.diagonal_one]
    | @insert a s ha ih =>
        intro comm
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Units.val_mul, ih]
        change Matrix.diagonal (Function.update (1 : Fin N → k) a (t : k))
            * Matrix.diagonal (fun j => if j ∈ s then (t : k) else 1)
            = Matrix.diagonal (fun j => if j ∈ insert a s then (t : k) else 1)
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hja : j = a
        · subst hja; simp [Function.update_self, ha]
        · rw [Function.update_of_ne hja]; simp [Finset.mem_insert, hja]
  rw [gen Finset.univ]
  change Matrix.diagonal (fun _ => (t : k))
      = Matrix.diagonal (fun j => if j ∈ (Finset.univ : Finset (Fin N)) then (t : k) else 1)
  simp



/-- An auxiliary component is contained in the eigenspace for the displayed power of the auxiliary unit. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryComponent_le_eigenspace
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N →₀ ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)
      ≤ Module.End.eigenspace (M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k))) ((GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k : k) ^ (∑ i, μ i)) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  have heig : ∀ i : Fin N, M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)) x = ((GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k : k) ^ μ i) • x := by
    intro i
    have hmem : x ∈ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun j => μ j) := hx
    rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace, Submodule.mem_iInf] at hmem
    have h2 := (Submodule.mem_iInf _).1 (hmem i) (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2
  have act : ∀ (s : Finset (Fin N))
      (comm : (↑s : Set (Fin N)).Pairwise
        fun a b => Commute (M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N a (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k))) (M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N b (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)))),
      (s.noncommProd (fun i => M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k))) comm) x
        = (∏ i ∈ s, (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k : k) ^ μ i) • x := by
    intro s
    induction s using Finset.induction with
    | empty => intro comm; simp
    | @insert a s ha ih =>
        intro comm
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Module.End.mul_apply, ih,
          Finset.prod_insert ha, map_smul, heig a, smul_smul, mul_comm]
  rw [GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryGeneralLinearElement_eq_noncommProd, Finset.map_noncommProd, act Finset.univ,
    Finset.prod_pow_eq_pow_sum]



variable (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))


/-- The auxiliary submodule indexed by a natural number over an algebraically closed field. -/
abbrev GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule (d : ℕ) : Submodule k M :=
  ⨆ (μ : Fin N →₀ ℕ) (_ : ∑ i, μ i = d), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i)


/-- The auxiliary submodule indexed by a natural number in characteristic zero. -/
abbrev GeneralLinearGroup.AuxiliaryDecomposition.characteristicZeroDegreeSubmodule (d : ℕ) : Submodule k M :=
  Module.End.eigenspace (M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k))) ((GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k : k) ^ d)

/-- The algebraically closed auxiliary degree submodule is contained in the characteristic-zero auxiliary degree submodule. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule_le_characteristicZeroDegreeSubmodule (d : ℕ) :
    GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d ≤ GeneralLinearGroup.AuxiliaryDecomposition.characteristicZeroDegreeSubmodule k N M d := by
  refine iSup₂_le (fun μ hμ => ?_)
  have h := GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryComponent_le_eigenspace k N M μ
  rwa [hμ] at h

/-- The characteristic-zero family of auxiliary degree submodules is supremum-independent. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.characteristicZeroDegreeSubmodule_iSupIndep : iSupIndep (GeneralLinearGroup.AuxiliaryDecomposition.characteristicZeroDegreeSubmodule k N M) :=
  (Module.End.eigenspaces_iSupIndep (M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)))).comp (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit_pow_injective k)

/-- If the displayed auxiliary components span, then the supremum of the algebraically closed degree submodules is top. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.iSup_algebraicallyClosedDegreeSubmodule_eq_top
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ d : ℕ, GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d = ⊤ := by
  rw [← h_span]
  apply le_antisymm
  · exact iSup_le (fun _ => iSup₂_le (fun μ _ =>
      le_iSup (fun ν : Fin N →₀ ℕ => RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => ν i)) μ))
  · exact iSup_le (fun μ => le_iSup_of_le (∑ i, μ i) (le_iSup₂_of_le μ rfl le_rfl))

/-- Under the spanning hypothesis, the two auxiliary degree-indexed submodule constructions agree. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule_eq_characteristicZeroDegreeSubmodule
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d = GeneralLinearGroup.AuxiliaryDecomposition.characteristicZeroDegreeSubmodule k N M d :=
  Submodule.family_eq_of_le_iSupIndep_iSup_eq_top (GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule_le_characteristicZeroDegreeSubmodule k N M)
    (GeneralLinearGroup.AuxiliaryDecomposition.characteristicZeroDegreeSubmodule_iSupIndep k N M) (GeneralLinearGroup.AuxiliaryDecomposition.iSup_algebraicallyClosedDegreeSubmodule_eq_top k N M h_span) d



/-- Each algebraically closed auxiliary degree submodule is stable under the general linear group action, assuming the displayed spanning condition. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule_stable
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤)
    (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ∀ x ∈ GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d, M.ρ g x ∈ GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d := by
  intro x hx
  rw [GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule_eq_characteristicZeroDegreeSubmodule k N M h_span] at hx ⊢
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hcomm : M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)) (M.ρ g x) = M.ρ g (M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)) x) := by
    have hmul : M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)) * M.ρ g = M.ρ g * M.ρ (RepresentationTheory.PolynomialMatrixCoefficients.RepresentationTheory.PolynomialMatrixCoefficients.Auxiliary.unitToGeneralLinearGroup k N (GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryUnit k)) := by
      rw [← map_mul, ← map_mul, GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryGeneralLinearElement_commutes]
    have := LinearMap.congr_fun hmul x
    rwa [Module.End.mul_apply, Module.End.mul_apply] at this
  rw [hcomm, hx, map_smul]


/-- The auxiliary subrepresentation indexed by a natural number constructed from a displayed spanning equality. -/
def GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    Subrepresentation M.ρ where
  toSubmodule := GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d
  apply_mem_toSubmodule g v hv := GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule_stable k N M h_span d g v hv





/-- The auxiliary component of a subrepresentation is the comap of the corresponding ambient auxiliary component. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryComponent_subrepresentation_eq_comap (σ : Subrepresentation M.ρ) (μ : Fin N → ℕ) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of σ.toRepresentation) μ
      = Submodule.comap σ.toSubmodule.subtype (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M μ) := by
  unfold RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace
  rw [Submodule.comap_iInf]
  refine iInf_congr (fun i => ?_)
  rw [Submodule.comap_iInf]
  refine iInf_congr (fun t => ?_)
  ext x
  have key : (((FDRep.of σ.toRepresentation).ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t)) x : M)
      = M.ρ (RepresentationTheory.GeneralLinearGroup.WeightCharacter.diagonalUnit k N i t) (x : M) := rfl
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.id_apply, Submodule.coe_subtype, Subtype.ext_iff, ZeroMemClass.coe_zero,
    Submodule.coe_sub, Submodule.coe_smul, key]




/-- Under the displayed hypotheses, each indexed auxiliary subrepresentation satisfies the indicated auxiliary property. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation_satisfiesAuxiliaryProperty
    (hpoly : RepresentationTheory.GeneralLinearGroup.DiagonalAction.IsAuxiliaryEndomorphismFamily N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N (FDRep.of (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).toRepresentation).ρ :=
  (hpoly.toAuxiliaryCondition).auxiliary_restrict (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).toSubmodule
    (fun g v hv => (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).apply_mem_toSubmodule g hv)


/-- A nonzero auxiliary component of an indexed auxiliary subrepresentation has index sum equal to its degree. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.sum_eq_degree_of_auxiliaryComponent_ne_bot
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) (d : ℕ)
    (μ : Fin N → ℕ)
    (hne : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).toRepresentation) μ ≠ ⊥) :
    ∑ i, μ i = d := by
  by_contra hsum
  apply hne
  rw [GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryComponent_subrepresentation_eq_comap]

  set ν : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm μ with hν
  have hνμ : (fun i => ν i) = μ := by funext i; simp [hν]
  have hsumν : ∑ i, ν i = ∑ i, μ i := by rw [hνμ]
  have hdis : Disjoint (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => ν i))
      (GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d) := by
    have hindep := RepresentationTheory.AuxiliaryCharacter.iSupIndep_auxiliaryWeightSpace k N M
    refine Disjoint.mono_right ?_ (hindep ν)
    refine iSup₂_le (fun ξ hξ => ?_)
    refine le_iSup₂_of_le ξ ?_ le_rfl
    intro h
    rw [h] at hξ
    exact hsum (hsumν ▸ hξ)
  rw [eq_bot_iff]
  rintro ⟨y, hymem⟩ hy
  rw [Submodule.mem_comap, Submodule.coe_subtype] at hy
  rw [hνμ] at hdis
  have hzero : y = 0 := hdis.le_bot (Submodule.mem_inf.mpr ⟨hy, hymem⟩)
  exact (Submodule.mem_bot k).mpr (Subtype.ext hzero)


/-- The auxiliary components of an indexed auxiliary subrepresentation span its ambient subrepresentation. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation_components_span
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    ⨆ (μ : Fin N →₀ ℕ),
        RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N (FDRep.of (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).toRepresentation) (fun i => μ i)
      = ⊤ := by
  simp_rw [GeneralLinearGroup.AuxiliaryDecomposition.auxiliaryComponent_subrepresentation_eq_comap]
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective _)
  rw [Submodule.map_iSup, Submodule.map_subtype_top]
  simp_rw [Submodule.map_comap_subtype]
  apply le_antisymm
  · exact iSup_le (fun _ => inf_le_left)
  · change GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d ≤ _
    refine iSup₂_le (fun ξ hξ => ?_)
    have hle : RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => ξ i) ≤ GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d :=
      le_iSup₂_of_le ξ hξ le_rfl
    calc RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => ξ i)
        = GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d ⊓ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => ξ i) := (inf_eq_right.mpr hle).symm
      _ ≤ ⨆ μ : Fin N →₀ ℕ, GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d ⊓ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) :=
          le_iSup
            (fun ν : Fin N →₀ ℕ => GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d ⊓ RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => ν i)) ξ



/-- A subrepresentation is semisimple as a module when its associated representation is semisimple. -/
theorem Subrepresentation.isSemisimpleModule_of_toRepresentation_isSemisimple
    {G W : Type*} [Monoid G] [AddCommGroup W] [Module k W]
    {ρ : Representation k G W} (σ : Subrepresentation ρ)
    (h : IsSemisimpleModule (MonoidAlgebra k G) σ.toRepresentation.asModule) :
    IsSemisimpleModule (MonoidAlgebra k G) (Subrepresentation.asSubmodule σ) := by
  haveI := h
  have hf : ∀ (g : G) (x : σ.toSubmodule),
      σ.toSubmodule.subtype (σ.toRepresentation g x) = ρ g (σ.toSubmodule.subtype x) :=
    fun _ _ => rfl
  let F := RepresentationTheory.AsModuleEquivalences.linearMapAsModule (ρ := σ.toRepresentation) (σ := ρ)
    σ.toSubmodule.subtype hf
  have hFinj : Function.Injective F := by
    intro a b hab
    refine Subtype.coe_injective ?_
    simpa [F, RepresentationTheory.AsModuleEquivalences.linearMapAsModule_apply] using hab
  have hrange : LinearMap.range F = Subrepresentation.asSubmodule σ := by
    apply SetLike.ext
    intro y
    simp only [LinearMap.mem_range, Subrepresentation.mem_asSubmodule_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have e : σ.toRepresentation.asModule ≃ₗ[MonoidAlgebra k G] Subrepresentation.asSubmodule σ :=
    (LinearEquiv.ofInjective F hFinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact IsSemisimpleModule.congr e.symm

/-- Under the displayed auxiliary and spanning hypotheses, every indexed auxiliary subrepresentation is semisimple as a module. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation_isSemisimpleModule
    (hpoly : RepresentationTheory.GeneralLinearGroup.DiagonalAction.IsAuxiliaryEndomorphismFamily N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N)
      (Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)) := by
  have hss : IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N)
      (Representation.asModule (FDRep.of (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).toRepresentation).ρ) :=
    GeneralLinearGroup.AuxiliaryDecomposition.isSemisimpleModule_of_auxiliaryConditions k N d (FDRep.of (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d).toRepresentation)
      (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation_satisfiesAuxiliaryProperty k N M hpoly h_span d)
      (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation_components_span k N M h_span d)
      (GeneralLinearGroup.AuxiliaryDecomposition.sum_eq_degree_of_auxiliaryComponent_ne_bot k N M h_span d)
  exact Subrepresentation.isSemisimpleModule_of_toRepresentation_isSemisimple (k := k) (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d) hss




/-- Restricting scalars on the underlying submodule of a subrepresentation leaves that submodule unchanged. -/
theorem Subrepresentation.restrictScalars_asSubmodule_eq_toSubmodule (σ : Subrepresentation M.ρ) :
    (Subrepresentation.asSubmodule σ).restrictScalars k = σ.toSubmodule := rfl

/-- The supremum of the indexed auxiliary subrepresentations is top. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.iSup_spanningAuxiliarySubrepresentation_eq_top
    (h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ d : ℕ, Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d) = ⊤ := by
  have h1 : (⨆ d : ℕ, Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)).restrictScalars k
      = ⊤ := by
    refine top_unique ?_
    calc (⊤ : Submodule k M)
        = ⨆ d : ℕ, GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d := (GeneralLinearGroup.AuxiliaryDecomposition.iSup_algebraicallyClosedDegreeSubmodule_eq_top k N M h_span).symm
      _ ≤ (⨆ d : ℕ, Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)).restrictScalars k := by
          refine iSup_le (fun d => ?_)
          calc GeneralLinearGroup.AuxiliaryDecomposition.algebraicallyClosedDegreeSubmodule k N M d
              = (Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)).restrictScalars k :=
                (Subrepresentation.restrictScalars_asSubmodule_eq_toSubmodule k N M (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)).symm
            _ ≤ (⨆ d : ℕ,
                  Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)).restrictScalars k :=
                Submodule.restrictScalars_mono (S := k)
                  (le_iSup (fun d => Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d)) d)
  have h2 := Submodule.restrictScalars_injective k (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N) (Representation.asModule M.ρ)
  apply h2
  rw [h1, Submodule.restrictScalars_top]







/-- The representation module is semisimple under the displayed auxiliary condition. -/
theorem GeneralLinearGroup.AuxiliaryDecomposition.isSemisimpleModule_of_auxiliaryCondition
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hpoly : RepresentationTheory.GeneralLinearGroup.DiagonalAction.IsAuxiliaryEndomorphismFamily N M.ρ) :
    IsSemisimpleModule (RepresentationTheory.Auxiliary.GeneralLinearGroupRepresentationDecomposition.Auxiliary.GeneralLinearGroupRepresentationDecomposition.auxiliaryFieldNatType k N) (Representation.asModule M.ρ) := by
  have h_span : ⨆ (μ : Fin N →₀ ℕ), RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N M (fun i => μ i) = ⊤ :=
    RepresentationTheory.GeneralLinearGroup.DiagonalAction.iSup_indexedFamily_eq_top_of_isAuxiliaryEndomorphismFamily M hpoly
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun d => Subrepresentation.asSubmodule (GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation k N M h_span d))
    (fun d => GeneralLinearGroup.AuxiliaryDecomposition.spanningAuxiliarySubrepresentation_isSemisimpleModule k N M hpoly h_span d)
    (GeneralLinearGroup.AuxiliaryDecomposition.iSup_spanningAuxiliarySubrepresentation_eq_top k N M h_span)

end RepresentationTheory.GeneralLinearGroup.AuxiliaryDecomposition

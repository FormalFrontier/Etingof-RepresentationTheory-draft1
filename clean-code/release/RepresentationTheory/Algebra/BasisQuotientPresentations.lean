/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Lie.AssociatedTypes
import RepresentationTheory.FreeAlgebra.RelationQuotient
import RepresentationTheory.LinearAlgebra.SymmetricTensors
import RepresentationTheory.Alignment.Attribute

/-! # Basis quotient presentations -/

namespace RepresentationTheory.Algebra.BasisQuotientPresentations

open scoped DirectSum TensorProduct

universe u v w

variable (k : Type u) [Field k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]
variable {ι : Type w} (b : Module.Basis ι k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The carrier of a relation-based symmetric-algebra model associated with a module over a commutative ring. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
abbrev SymmetricAlgebra.RelationModel (k : Type*) (V : Type*) [CommRing k]
    [AddCommGroup V] [Module k V] :=
  SymmetricAlgebra k V

/-- The carrier of a relation-based exterior-algebra model associated with a module over a commutative ring. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
abbrev ExteriorAlgebra.RelationModel (k : Type*) (V : Type*) [CommRing k]
    [AddCommGroup V] [Module k V] :=
  ExteriorAlgebra k V

/-- A basis-independent quotient model for the associative envelope of a Lie algebra over a commutative ring. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
abbrev UniversalEnvelopingAlgebra.QuotientModel (k : Type*) (L : Type*) [CommRing k]
    [LieRing L] [LieAlgebra k L] :=
  UniversalEnvelopingAlgebra k L

/-- Canonical generators of a symmetric algebra commute with one another. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
theorem SymmetricAlgebra.generator_mul_comm (V : Type v) [AddCommGroup V] [Module k V]
    (x y : V) :
    SymmetricAlgebra.ι k V x * SymmetricAlgebra.ι k V y =
      SymmetricAlgebra.ι k V y * SymmetricAlgebra.ι k V x :=
  mul_comm _ _

/-- Every canonical exterior-algebra generator has square zero. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
theorem ExteriorAlgebra.generator_sq_eq_zero (V : Type v) [AddCommGroup V] [Module k V]
    (x : V) :
    ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k x = 0 :=
  ExteriorAlgebra.ι_sq_zero x

/-- The commutator of two canonical enveloping generators equals the generator associated with their Lie bracket. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
theorem UniversalEnvelopingAlgebra.generator_commutator (x y : L) :
    UniversalEnvelopingAlgebra.ι k x * UniversalEnvelopingAlgebra.ι k y -
        UniversalEnvelopingAlgebra.ι k y * UniversalEnvelopingAlgebra.ι k x =
      UniversalEnvelopingAlgebra.ι k ⁅x, y⁆ := by
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]

/-- A chosen basis identifies the symmetric relation model with the multivariable polynomial algebra on the basis indices. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def SymmetricAlgebra.relationModelEquivMvPolynomial
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) :
    SymmetricAlgebra.RelationModel k V ≃ₐ[k] MvPolynomial ι k :=
  SymmetricAlgebra.equivMvPolynomial b

/-- The polynomial equivalence sends the symmetric-algebra image of a basis vector to the corresponding indeterminate. -/
@[simp] theorem SymmetricAlgebra.relationModelEquivMvPolynomial_apply_basis
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) (i : ι) :
    SymmetricAlgebra.relationModelEquivMvPolynomial k V b (SymmetricAlgebra.ι k V (b i)) =
      MvPolynomial.X i :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply b i

/-- A chosen basis identifies the exterior relation model with the exterior algebra on finitely supported coordinates. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def ExteriorAlgebra.relationModelEquivFinsupp
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) :
    ExteriorAlgebra.RelationModel k V ≃ₐ[k] ExteriorAlgebra k (ι →₀ k) :=
  CliffordAlgebra.equivOfIsometry
    ({ toLinearEquiv := b.repr, map_app' := fun _ => rfl } :
      QuadraticMap.IsometryEquiv (0 : QuadraticForm k V) (0 : QuadraticForm k (ι →₀ k)))

/-- Under the coordinate equivalence, an exterior generator maps to the generator determined by its basis representation. -/
@[simp] theorem ExteriorAlgebra.relationModelEquivFinsupp_apply
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) (x : V) :
    ExteriorAlgebra.relationModelEquivFinsupp k V b (ExteriorAlgebra.ι k x) =
      ExteriorAlgebra.ι k (b.repr x) := by
  rw [ExteriorAlgebra.relationModelEquivFinsupp, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  rfl

/-- An auxiliary construction whose formal type is unavailable in rendered form. -/
noncomputable def Algebra.BasisQuotientPresentations.unrenderedAuxiliary (ι : Type w) :
    (ι →₀ ℕ) ≃ Σ n : ℕ, Sym ι n := by
  classical
  exact (Equiv.sigmaFiberEquiv (fun f : ι →₀ ℕ => f.sum fun _ m => m)).symm.trans
    (Equiv.sigmaCongrRight fun n => (Sym.equivNatSum ι n).symm)

/-- A basis-dependent linear equivalence between the symmetric relation model and its degree-indexed direct sum. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def SymmetricAlgebra.relationModelGradedEquiv
    (V : Type v) [AddCommGroup V] [Module k V] {ι : Type w} (b : Module.Basis ι k V) :
    SymmetricAlgebra.RelationModel k V ≃ₗ[k]
      ⨁ n : ℕ, RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n :=
  b.symmetricAlgebra.repr ≪≫ₗ
    Finsupp.domLCongr (Algebra.BasisQuotientPresentations.unrenderedAuxiliary ι) ≪≫ₗ
    sigmaFinsuppLequivDFinsupp k ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun n =>
      (RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux1 b n).repr.symm

/-- A linear equivalence between the exterior relation model and the direct sum of its degree-indexed components. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def ExteriorAlgebra.relationModelGradedEquiv
    (V : Type v) [AddCommGroup V] [Module k V] :
    ExteriorAlgebra.RelationModel k V ≃ₗ[k]
      ⨁ n : ℕ, RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V n :=
  DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[k]^n V) ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun n =>
      RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv n

/-- The free-algebra relation assigned to a pair of basis indices for a Lie algebra. -/
@[source_ref "Chapter2/Definition2.9.9" (role := primary)]
noncomputable def UniversalEnvelopingAlgebra.basisRelations (ij : ι × ι) : FreeAlgebra k ι :=
  FreeAlgebra.ι k ij.1 * FreeAlgebra.ι k ij.2 -
    FreeAlgebra.ι k ij.2 * FreeAlgebra.ι k ij.1 -
      (b.repr ⁅b ij.1, b ij.2⁆).sum fun r a => a • FreeAlgebra.ι k r

/-- A basis-indexed quotient model for the associative envelope of a Lie algebra over a field. -/
@[source_ref "Chapter2/Definition2.9.9/Derived2" (role := supporting)]
abbrev UniversalEnvelopingAlgebra.BasisQuotientModel :=
  RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType k ι (ι × ι)
    (UniversalEnvelopingAlgebra.basisRelations k L b)

/-- The canonical algebra homomorphism from the basis-indexed quotient model to the basis-independent enveloping model. -/
noncomputable def UniversalEnvelopingAlgebra.basisQuotientToQuotientModel :
    UniversalEnvelopingAlgebra.BasisQuotientModel k L b →ₐ[k]
      UniversalEnvelopingAlgebra.QuotientModel k L :=
  RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.lift
    (UniversalEnvelopingAlgebra.basisRelations k L b)
    (fun i => UniversalEnvelopingAlgebra.ι k (b i)) (by
      rintro ⟨i, j⟩
      simp only [UniversalEnvelopingAlgebra.basisRelations, map_sub, map_mul,
        FreeAlgebra.lift_ι_apply]
      simp only [Finsupp.sum, map_sum, map_smul, FreeAlgebra.lift_ι_apply]
      have hbexp : (b.repr ⁅b i, b j⁆).sum (fun r a => a • b r) = ⁅b i, b j⁆ := by
        change Finsupp.linearCombination k b (b.repr ⁅b i, b j⁆) = ⁅b i, b j⁆
        rw [← Module.Basis.repr_symm_apply, b.repr.symm_apply_apply]
      rw [sub_eq_zero]
      symm
      calc
        ∑ r ∈ (b.repr ⁅b i, b j⁆).support,
            (b.repr ⁅b i, b j⁆) r • UniversalEnvelopingAlgebra.ι k (b r) =
            UniversalEnvelopingAlgebra.ι k
              ((b.repr ⁅b i, b j⁆).sum (fun r a => a • b r)) := by
          simp only [Finsupp.sum, map_sum, map_smul]
        _ = UniversalEnvelopingAlgebra.ι k ⁅b i, b j⁆ :=
          congrArg (UniversalEnvelopingAlgebra.ι k) hbexp
        _ = ⁅UniversalEnvelopingAlgebra.ι k (b i),
              UniversalEnvelopingAlgebra.ι k (b j)⁆ := LieHom.map_lie _ _ _
        _ = UniversalEnvelopingAlgebra.ι k (b i) *
              UniversalEnvelopingAlgebra.ι k (b j) -
              UniversalEnvelopingAlgebra.ι k (b j) *
                UniversalEnvelopingAlgebra.ι k (b i) :=
          LieRing.of_associative_ring_bracket _ _)

/-- The linear map underlying the canonical generator map into the basis-indexed quotient model. -/
noncomputable def UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap : L →ₗ[k]
    UniversalEnvelopingAlgebra.BasisQuotientModel k L b :=
  (b.constr k)
    (RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
      (UniversalEnvelopingAlgebra.basisRelations k L b))

/-- The generator linear map sends a basis vector to the quotient element indexed by the same coordinate. -/
@[simp] theorem UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap_apply_basis (i : ι) :
    UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b (b i) =
      RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
        (UniversalEnvelopingAlgebra.basisRelations k L b) i :=
  Module.Basis.constr_basis b k _ i

/-- The canonical Lie homomorphism from a Lie algebra into its basis-indexed quotient model. -/
noncomputable def UniversalEnvelopingAlgebra.basisQuotientGeneratorLieHom : L →ₗ⁅k⁆
    UniversalEnvelopingAlgebra.BasisQuotientModel k L b :=
  { UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b with
    map_lie' := by
      intro x y
      let lhs : L →ₗ[k] L →ₗ[k] UniversalEnvelopingAlgebra.BasisQuotientModel k L b :=
        LinearMap.mk₂ k (fun x y =>
          UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b ⁅x, y⁆)
          (by simp) (by simp) (by simp) (by simp)
      let rhs : L →ₗ[k] L →ₗ[k] UniversalEnvelopingAlgebra.BasisQuotientModel k L b :=
        LinearMap.mk₂ k (fun x y =>
          ⁅UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b x,
            UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b y⁆)
          (by simp) (by simp) (by simp)
          (by
            intro c x y
            rw [map_smul]
            exact lie_smul c
              (UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b x)
              (UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b y))
      have hbilin : lhs = rhs := by
        apply Module.Basis.ext b
        intro i
        apply Module.Basis.ext b
        intro j
        change UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b ⁅b i, b j⁆ =
          ⁅UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b (b i),
            UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b (b j)⁆
        rw [UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap_apply_basis,
          UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap_apply_basis,
          UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap, Module.Basis.constr_apply]
        have hrel :=
          RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.auxiliaryAlgHom_relation
            (UniversalEnvelopingAlgebra.basisRelations k L b) (i, j)
        simp only [UniversalEnvelopingAlgebra.basisRelations, map_sub, map_mul,
          Finsupp.sum, map_sum, map_smul] at hrel
        rw [LieRing.of_associative_ring_bracket]
        exact (sub_eq_zero.mp hrel).symm
      exact congrArg (fun F => F x y) hbilin }

/-- The canonical algebra homomorphism from the basis-independent enveloping model to the basis-indexed quotient model. -/
noncomputable def UniversalEnvelopingAlgebra.quotientModelToBasisQuotient :
    UniversalEnvelopingAlgebra.QuotientModel k L →ₐ[k]
      UniversalEnvelopingAlgebra.BasisQuotientModel k L b :=
  UniversalEnvelopingAlgebra.lift k
    (UniversalEnvelopingAlgebra.basisQuotientGeneratorLieHom k L b)

/-- The canonical reverse map sends an indexed quotient generator to the enveloping image of the associated basis vector. -/
@[simp] theorem UniversalEnvelopingAlgebra.basisQuotientToQuotientModel_apply (i : ι) :
    UniversalEnvelopingAlgebra.basisQuotientToQuotientModel k L b
        (RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
          (UniversalEnvelopingAlgebra.basisRelations k L b) i) =
      UniversalEnvelopingAlgebra.ι k (b i) := by
  simp [UniversalEnvelopingAlgebra.basisQuotientToQuotientModel]

/-- The canonical forward map carries each enveloping generator to its image under the basis-quotient generator map. -/
theorem UniversalEnvelopingAlgebra.quotientModelToBasisQuotient_apply (x : L) :
    UniversalEnvelopingAlgebra.quotientModelToBasisQuotient k L b
        (UniversalEnvelopingAlgebra.ι k x) =
      UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b x := by
  rw [UniversalEnvelopingAlgebra.quotientModelToBasisQuotient,
    UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- A basis-dependent algebra equivalence from the indexed relation quotient to the corresponding enveloping algebra. -/
@[source_ref "Chapter2/Remark2.9.10" (role := primary),
  source_ref "Chapter2/Definition2.12.1" (role := primary),
  source_ref "Chapter2/Definition2.9.9/Derived2" (role := supporting)]
noncomputable def UniversalEnvelopingAlgebra.basisQuotientEquivEnvelope :
    UniversalEnvelopingAlgebra.BasisQuotientModel k L b ≃ₐ[k]
      RepresentationTheory.Algebra.Lie.AssociatedTypes.LieAlgebra.AuxiliaryType k L :=
  AlgEquiv.ofAlgHom
    (UniversalEnvelopingAlgebra.basisQuotientToQuotientModel k L b)
    (UniversalEnvelopingAlgebra.quotientModelToBasisQuotient k L b)
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      rw [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        UniversalEnvelopingAlgebra.quotientModelToBasisQuotient_apply]
      change UniversalEnvelopingAlgebra.basisQuotientToQuotientModel k L b
        (UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b x) = _
      rw [UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap,
        Module.Basis.constr_apply]
      simp only [Finsupp.sum, map_sum, map_smul,
        UniversalEnvelopingAlgebra.basisQuotientToQuotientModel_apply]
      have hbexp : (b.repr x).sum (fun r a => a • b r) = x := by
        change Finsupp.linearCombination k b (b.repr x) = x
        rw [← Module.Basis.repr_symm_apply, b.repr.symm_apply_apply]
      calc
        ∑ r ∈ (b.repr x).support,
            (b.repr x) r • UniversalEnvelopingAlgebra.ι k (b r) =
            UniversalEnvelopingAlgebra.ι k ((b.repr x).sum (fun r a => a • b r)) := by
          simp only [Finsupp.sum, map_sum, map_smul]
        _ = UniversalEnvelopingAlgebra.ι k x :=
          congrArg (UniversalEnvelopingAlgebra.ι k) hbexp)
    (by
      apply RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.algHom_ext
        (UniversalEnvelopingAlgebra.basisRelations k L b)
      intro i
      rw [AlgHom.comp_apply,
        UniversalEnvelopingAlgebra.basisQuotientToQuotientModel_apply,
        UniversalEnvelopingAlgebra.quotientModelToBasisQuotient_apply,
        UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap_apply_basis]
      rfl)

/-- A map from the basis quotient to the enveloping algebra is canonical when it has the prescribed value on every indexed generator. -/
theorem UniversalEnvelopingAlgebra.basisQuotientToEnvelope_unique
    (F : UniversalEnvelopingAlgebra.BasisQuotientModel k L b →ₐ[k]
      RepresentationTheory.Algebra.Lie.AssociatedTypes.LieAlgebra.AuxiliaryType k L)
    (hF : ∀ i, F
      (RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
        (UniversalEnvelopingAlgebra.basisRelations k L b) i) =
      UniversalEnvelopingAlgebra.ι k (b i)) :
    F = UniversalEnvelopingAlgebra.basisQuotientToQuotientModel k L b := by
  apply RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.algHom_ext
    (UniversalEnvelopingAlgebra.basisRelations k L b)
  intro i
  rw [hF, UniversalEnvelopingAlgebra.basisQuotientToQuotientModel_apply]

/-- An algebra homomorphism into the basis quotient is canonical if it agrees with the generator linear map on every Lie-algebra element. -/
theorem UniversalEnvelopingAlgebra.quotientModelToBasisQuotient_unique
    (F : UniversalEnvelopingAlgebra.QuotientModel k L →ₐ[k]
      UniversalEnvelopingAlgebra.BasisQuotientModel k L b)
    (hF : ∀ x, F (UniversalEnvelopingAlgebra.ι k x) =
      UniversalEnvelopingAlgebra.basisQuotientGeneratorLinearMap k L b x) :
    F = UniversalEnvelopingAlgebra.quotientModelToBasisQuotient k L b := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  change F (UniversalEnvelopingAlgebra.ι k x) =
    UniversalEnvelopingAlgebra.quotientModelToBasisQuotient k L b
      (UniversalEnvelopingAlgebra.ι k x)
  rw [hF, UniversalEnvelopingAlgebra.quotientModelToBasisQuotient_apply]

end RepresentationTheory.Algebra.BasisQuotientPresentations

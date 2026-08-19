/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Lie.AssociatedTypes
import RepresentationTheory.FreeAlgebra.RelationQuotient
import RepresentationTheory.LinearAlgebra.SymmetricTensors
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary Lie-module constructions -/

namespace RepresentationTheory.Algebra.AuxiliaryLieModuleConstructions

open scoped DirectSum TensorProduct

universe u v w

variable (k : Type u) [Field k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]
variable {ι : Type w} (b : Module.Basis ι k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- An auxiliary type associated with a module over a commutative ring. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
abbrev SymmetricAlgebra.auxiliaryModel (k : Type*) (V : Type*) [CommRing k]
    [AddCommGroup V] [Module k V] :=
  SymmetricAlgebra k V

/-- An auxiliary type associated with a module over a commutative ring. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
abbrev ExteriorAlgebra.auxiliaryModel (k : Type*) (V : Type*) [CommRing k]
    [AddCommGroup V] [Module k V] :=
  ExteriorAlgebra k V

/-- An auxiliary type depending on a Lie algebra over a commutative ring. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
abbrev UniversalEnvelopingAlgebra.auxiliaryType (k : Type*) (L : Type*) [CommRing k]
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
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
theorem ExteriorAlgebra.generator_sq_eq_zero (V : Type v) [AddCommGroup V] [Module k V]
    (x : V) :
    ExteriorAlgebra.ι k x * ExteriorAlgebra.ι k x = 0 :=
  ExteriorAlgebra.ι_sq_zero x

/-- The commutator of two canonical enveloping generators equals the generator associated with their Lie bracket. -/
@[source_ref "Chapter2/Definition2.12.1" (role := supporting)]
theorem UniversalEnvelopingAlgebra.generator_commutator (x y : L) :
    UniversalEnvelopingAlgebra.ι k x * UniversalEnvelopingAlgebra.ι k y -
        UniversalEnvelopingAlgebra.ι k y * UniversalEnvelopingAlgebra.ι k x =
      UniversalEnvelopingAlgebra.ι k ⁅x, y⁆ := by
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]

/-- An algebra equivalence from an auxiliary type to multivariable polynomials on the basis indices. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def SymmetricAlgebra.auxiliaryModelEquivMvPolynomial
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) :
    SymmetricAlgebra.auxiliaryModel k V ≃ₐ[k] MvPolynomial ι k :=
  SymmetricAlgebra.equivMvPolynomial b

/-- Gives the value of the displayed algebra equivalence on the image of a basis vector. -/
@[simp] theorem SymmetricAlgebra.auxiliaryModelEquivMvPolynomial_apply_basis
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) (i : ι) :
    SymmetricAlgebra.auxiliaryModelEquivMvPolynomial k V b (SymmetricAlgebra.ι k V (b i)) =
      MvPolynomial.X i :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply b i

/-- An algebra equivalence from an auxiliary type to an exterior algebra on finitely supported coordinates. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def ExteriorAlgebra.auxiliaryModelEquivFinsupp
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) :
    ExteriorAlgebra.auxiliaryModel k V ≃ₐ[k] ExteriorAlgebra k (ι →₀ k) :=
  CliffordAlgebra.equivOfIsometry
    ({ toLinearEquiv := b.repr, map_app' := fun _ => rfl } :
      QuadraticMap.IsometryEquiv (0 : QuadraticForm k V) (0 : QuadraticForm k (ι →₀ k)))

/-- Gives the value of the displayed algebra equivalence on an exterior-algebra generator. -/
@[simp] theorem ExteriorAlgebra.auxiliaryModelEquivFinsupp_apply
    (V : Type v) [AddCommGroup V] [Module k V]
    {ι : Type w} (b : Module.Basis ι k V) (x : V) :
    ExteriorAlgebra.auxiliaryModelEquivFinsupp k V b (ExteriorAlgebra.ι k x) =
      ExteriorAlgebra.ι k (b.repr x) := by
  rw [ExteriorAlgebra.auxiliaryModelEquivFinsupp, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  rfl

/-- An auxiliary construction whose formal type is unavailable in rendered form. -/
noncomputable def unrenderedAuxiliary (ι : Type w) :
    (ι →₀ ℕ) ≃ Σ n : ℕ, Sym ι n := by
  classical
  exact (Equiv.sigmaFiberEquiv (fun f : ι →₀ ℕ => f.sum fun _ m => m)).symm.trans
    (Equiv.sigmaCongrRight fun n => (Sym.equivNatSum ι n).symm)

/-- A basis-dependent linear equivalence from an auxiliary type to the displayed Nat-indexed direct sum. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def SymmetricAlgebra.auxiliaryModelDirectSumEquiv
    (V : Type v) [AddCommGroup V] [Module k V] {ι : Type w} (b : Module.Basis ι k V) :
    SymmetricAlgebra.auxiliaryModel k V ≃ₗ[k]
      ⨁ n : ℕ, RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux1 k V n :=
  b.symmetricAlgebra.repr ≪≫ₗ
    Finsupp.domLCongr (unrenderedAuxiliary ι) ≪≫ₗ
    sigmaFinsuppLequivDFinsupp k ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun n =>
      (RepresentationTheory.LinearAlgebra.SymmetricTensors.distinguishedElement_aux1 b n).repr.symm

/-- A linear equivalence from an auxiliary type to the displayed Nat-indexed direct sum. -/
@[source_ref "Chapter2/Definition2.12.1" (role := primary)]
noncomputable def ExteriorAlgebra.auxiliaryModelDirectSumEquiv
    (V : Type v) [AddCommGroup V] [Module k V] :
    ExteriorAlgebra.auxiliaryModel k V ≃ₗ[k]
      ⨁ n : ℕ, RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType k V n :=
  DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[k]^n V) ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun n =>
      RepresentationTheory.LinearAlgebra.TensorOperations.linearEquiv n

/-- An element of a free algebra associated with a basis and a pair of basis indices. -/
@[source_ref "Chapter2/Definition2.9.9" (role := supporting)]
noncomputable def UniversalEnvelopingAlgebra.auxiliaryBasisPairElement (ij : ι × ι) : FreeAlgebra k ι :=
  FreeAlgebra.ι k ij.1 * FreeAlgebra.ι k ij.2 -
    FreeAlgebra.ι k ij.2 * FreeAlgebra.ι k ij.1 -
      (b.repr ⁅b ij.1, b ij.2⁆).sum fun r a => a • FreeAlgebra.ι k r

/-- An auxiliary type depending on a Lie algebra over a field and a chosen basis. -/
@[source_ref "Chapter2/Definition2.9.9/Derived2" (role := supporting)]
abbrev UniversalEnvelopingAlgebra.auxiliaryBasisType :=
  RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType k ι (ι × ι)
    (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b)

/-- An algebra homomorphism between the two auxiliary types displayed in its type. -/
noncomputable def UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom :
    UniversalEnvelopingAlgebra.auxiliaryBasisType k L b →ₐ[k]
      UniversalEnvelopingAlgebra.auxiliaryType k L :=
  RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.lift
    (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b)
    (fun i => UniversalEnvelopingAlgebra.ι k (b i)) (by
      rintro ⟨i, j⟩
      simp only [UniversalEnvelopingAlgebra.auxiliaryBasisPairElement, map_sub, map_mul,
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

/-- A linear map from a Lie algebra to the auxiliary type determined by a basis. -/
noncomputable def UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap : L →ₗ[k]
    UniversalEnvelopingAlgebra.auxiliaryBasisType k L b :=
  (b.constr k)
    (RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
      (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b))

/-- States the value of the auxiliary linear map at a selected basis vector. -/
@[simp] theorem UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap_apply_basis (i : ι) :
    UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b (b i) =
      RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
        (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b) i :=
  Module.Basis.constr_basis b k _ i

/-- A Lie homomorphism from a Lie algebra to the auxiliary type determined by a basis. -/
noncomputable def UniversalEnvelopingAlgebra.auxiliaryBasisLieHom : L →ₗ⁅k⁆
    UniversalEnvelopingAlgebra.auxiliaryBasisType k L b :=
  { UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b with
    map_lie' := by
      intro x y
      let lhs : L →ₗ[k] L →ₗ[k] UniversalEnvelopingAlgebra.auxiliaryBasisType k L b :=
        LinearMap.mk₂ k (fun x y =>
          UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b ⁅x, y⁆)
          (by simp) (by simp) (by simp) (by simp)
      let rhs : L →ₗ[k] L →ₗ[k] UniversalEnvelopingAlgebra.auxiliaryBasisType k L b :=
        LinearMap.mk₂ k (fun x y =>
          ⁅UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b x,
            UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b y⁆)
          (by simp) (by simp) (by simp)
          (by
            intro c x y
            rw [map_smul]
            exact lie_smul c
              (UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b x)
              (UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b y))
      have hbilin : lhs = rhs := by
        apply Module.Basis.ext b
        intro i
        apply Module.Basis.ext b
        intro j
        change UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b ⁅b i, b j⁆ =
          ⁅UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b (b i),
            UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b (b j)⁆
        rw [UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap_apply_basis,
          UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap_apply_basis,
          UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap, Module.Basis.constr_apply]
        have hrel :=
          RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.auxiliaryAlgHom_relation
            (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b) (i, j)
        simp only [UniversalEnvelopingAlgebra.auxiliaryBasisPairElement, map_sub, map_mul,
          Finsupp.sum, map_sum, map_smul] at hrel
        rw [LieRing.of_associative_ring_bracket]
        exact (sub_eq_zero.mp hrel).symm
      exact congrArg (fun F => F x y) hbilin }

/-- An algebra homomorphism between the two auxiliary types displayed in its type. -/
noncomputable def UniversalEnvelopingAlgebra.auxiliaryAlgHom :
    UniversalEnvelopingAlgebra.auxiliaryType k L →ₐ[k]
      UniversalEnvelopingAlgebra.auxiliaryBasisType k L b :=
  UniversalEnvelopingAlgebra.lift k
    (UniversalEnvelopingAlgebra.auxiliaryBasisLieHom k L b)

/-- Gives the value of the auxiliary algebra homomorphism on a displayed basis-indexed input. -/
@[simp] theorem UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom_apply (i : ι) :
    UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom k L b
        (RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
          (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b) i) =
      UniversalEnvelopingAlgebra.ι k (b i) := by
  simp [UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom]

/-- Gives the value of the auxiliary algebra homomorphism on a displayed input. -/
theorem UniversalEnvelopingAlgebra.auxiliaryAlgHom_apply (x : L) :
    UniversalEnvelopingAlgebra.auxiliaryAlgHom k L b
        (UniversalEnvelopingAlgebra.ι k x) =
      UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b x := by
  rw [UniversalEnvelopingAlgebra.auxiliaryAlgHom,
    UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- A basis-dependent algebra equivalence between the two auxiliary types displayed in its type. -/
@[source_ref "Chapter2/Remark2.9.10" (role := primary),
  source_ref "Chapter2/Definition2.12.1" (role := primary),
  source_ref "Chapter2/Definition2.9.9/Derived2" (role := supporting)]
noncomputable def UniversalEnvelopingAlgebra.auxiliaryBasisEquiv :
    UniversalEnvelopingAlgebra.auxiliaryBasisType k L b ≃ₐ[k]
      RepresentationTheory.Algebra.Lie.AssociatedTypes.LieAlgebra.AuxiliaryType k L :=
  AlgEquiv.ofAlgHom
    (UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom k L b)
    (UniversalEnvelopingAlgebra.auxiliaryAlgHom k L b)
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      rw [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        UniversalEnvelopingAlgebra.auxiliaryAlgHom_apply]
      change UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom k L b
        (UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b x) = _
      rw [UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap,
        Module.Basis.constr_apply]
      simp only [Finsupp.sum, map_sum, map_smul,
        UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom_apply]
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
        (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b)
      intro i
      rw [AlgHom.comp_apply,
        UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom_apply,
        UniversalEnvelopingAlgebra.auxiliaryAlgHom_apply,
        UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap_apply_basis]
      rfl)

/-- An algebra homomorphism is equal to the displayed auxiliary homomorphism when the stated values on every index agree. -/
theorem UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom_unique
    (F : UniversalEnvelopingAlgebra.auxiliaryBasisType k L b →ₐ[k]
      RepresentationTheory.Algebra.Lie.AssociatedTypes.LieAlgebra.AuxiliaryType k L)
    (hF : ∀ i, F
      (RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of
        (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b) i) =
      UniversalEnvelopingAlgebra.ι k (b i)) :
    F = UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom k L b := by
  apply RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.algHom_ext
    (UniversalEnvelopingAlgebra.auxiliaryBasisPairElement k L b)
  intro i
  rw [hF, UniversalEnvelopingAlgebra.auxiliaryBasisAlgHom_apply]

/-- An algebra homomorphism is equal to the displayed auxiliary homomorphism when the stated pointwise condition holds. -/
theorem UniversalEnvelopingAlgebra.auxiliaryAlgHom_unique
    (F : UniversalEnvelopingAlgebra.auxiliaryType k L →ₐ[k]
      UniversalEnvelopingAlgebra.auxiliaryBasisType k L b)
    (hF : ∀ x, F (UniversalEnvelopingAlgebra.ι k x) =
      UniversalEnvelopingAlgebra.auxiliaryBasisLinearMap k L b x) :
    F = UniversalEnvelopingAlgebra.auxiliaryAlgHom k L b := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  change F (UniversalEnvelopingAlgebra.ι k x) =
    UniversalEnvelopingAlgebra.auxiliaryAlgHom k L b
      (UniversalEnvelopingAlgebra.ι k x)
  rw [hF, UniversalEnvelopingAlgebra.auxiliaryAlgHom_apply]

end RepresentationTheory.Algebra.AuxiliaryLieModuleConstructions

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Group.SimpleRepresentations

open scoped MonoidAlgebra TensorProduct
open CategoryTheory

namespace RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences

universe u v w w'

section Transport

variable {k : Type u} [CommRing k] {R : Type*} [Ring R] [Algebra k R]
  {M : Type w} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  {N : Type w'} [AddCommGroup N] [Module k N]

/-- A module structure transported across a linear equivalence to its target. -/
@[reducible]
def moduleTransportAlongLinearEquiv (e : M ≃ₗ[k] N) : Module R N where
  smul r y := e (r • e.symm y)
  one_smul y := by
    change e (1 • e.symm y) = y
    rw [one_smul, e.apply_symm_apply]
  mul_smul r s y := by
    change e ((r * s) • e.symm y) = e (r • e.symm (e (s • e.symm y)))
    rw [e.symm_apply_apply, mul_smul]
  smul_zero r := by
    change e (r • e.symm 0) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add r y z := by
    change e (r • e.symm (y + z)) = e (r • e.symm y) + e (r • e.symm z)
    rw [map_add, smul_add, map_add]
  add_smul r s y := by
    change e ((r + s) • e.symm y) = e (r • e.symm y) + e (s • e.symm y)
    rw [add_smul, map_add]
  zero_smul y := by
    change e ((0 : R) • e.symm y) = 0
    rw [zero_smul, map_zero]

/-- Transporting a module structure across a base-linear equivalence preserves the compatible
scalar-tower structure. -/
theorem isScalarTower_moduleTransportAlongLinearEquiv (e : M ≃ₗ[k] N) :
    @IsScalarTower k R N _ (moduleTransportAlongLinearEquiv e).toSMul _ := by
  letI := moduleTransportAlongLinearEquiv (k := k) (R := R) e
  refine ⟨fun c r y => ?_⟩
  change e ((c • r) • e.symm y) = c • e (r • e.symm y)
  rw [smul_assoc, map_smul]

/-- A linear equivalence becomes linear over a second ring after transporting the source module
structure to the target. -/
def linearEquiv_transportModule (e : M ≃ₗ[k] N) :
    letI := moduleTransportAlongLinearEquiv (k := k) (R := R) e
    M ≃ₗ[R] N :=
  letI := moduleTransportAlongLinearEquiv (k := k) (R := R) e
  { e.toAddEquiv with
    map_smul' := fun r x => by
      change e (r • x) = e (r • e.symm (e x))
      rw [LinearEquiv.symm_apply_apply] }

end Transport

section RepresentationOfMonoidAlgebraModule

variable {k : Type u} [Field k] {G : Type v} [Group G]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]

/-- The group representation associated with a compatible module over the monoid algebra. -/
noncomputable def representationOfMonoidAlgebraModule : Representation k G M :=
  (Algebra.lsmul k k M : MonoidAlgebra k G →ₐ[k] Module.End k M).toRingHom.toMonoidHom.comp
    (MonoidAlgebra.of k G)

/-- The associated representation acts by the monoid-algebra element supported at the group
element with coefficient one. -/
theorem representationOfMonoidAlgebraModule_apply (g : G) (x : M) :
    representationOfMonoidAlgebraModule (k := k) (G := G) M g x =
      MonoidAlgebra.single g (1 : k) • x :=
  rfl

/-- The algebra homomorphism of the associated representation is scalar multiplication by the
monoid algebra. -/
theorem asAlgebraHom_representationOfMonoidAlgebraModule :
    (representationOfMonoidAlgebraModule (k := k) (G := G) M).asAlgebraHom =
      Algebra.lsmul k k M := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    rw [Representation.asAlgebraHom_single_one]
    rfl
  · ext

/-- The module underlying the associated representation is linearly equivalent to the original
monoid-algebra module. -/
noncomputable def asModuleRepresentationOfMonoidAlgebraModule :
    (representationOfMonoidAlgebraModule (k := k) (G := G) M).asModule
      ≃ₗ[MonoidAlgebra k G] M :=
  { (representationOfMonoidAlgebraModule
      (k := k) (G := G) M).asModuleEquiv.toAddEquiv with
    map_smul' := fun r x => by
      change (representationOfMonoidAlgebraModule
          (k := k) (G := G) M).asModuleEquiv (r • x) =
        r • (representationOfMonoidAlgebraModule
          (k := k) (G := G) M).asModuleEquiv x
      rw [Representation.asModuleEquiv_map_smul,
        asAlgebraHom_representationOfMonoidAlgebraModule]
      rfl }

end RepresentationOfMonoidAlgebraModule

section RepresentationEquivOfModule

variable {k : Type u} [Field k] {G : Type v} [Group G]
  {V : Type w} [AddCommGroup V] [Module k V]
  {W : Type w'} [AddCommGroup W] [Module k W]

open _root_.Representation

/-- A linear equivalence of the modules associated with two representations induces an
equivalence of those representations. -/
noncomputable def representationEquivOfModuleLinearEquiv
    (ρ : Representation k G V) (σ : Representation k G W)
    (f : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) : ρ.Equiv σ :=
  ((IntertwiningMap.equivLinearMapAsModule ρ σ).symm f.toLinearMap).ofBijective f.bijective

end RepresentationEquivOfModule

section Count

open MonoidAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Invertible (Fintype.card G : k)]

/-- An isomorphism between the finite-dimensional representations obtained from two group-algebra
modules induces a module-linear equivalence. -/
noncomputable def moduleLinearEquivOfFDRepIso
    {M N : Type u} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]
    [AddCommGroup N] [Module k N] [Module.Finite k N]
    [Module (MonoidAlgebra k G) N] [IsScalarTower k (MonoidAlgebra k G) N]
    (α : FDRep.of (representationOfMonoidAlgebraModule (k := k) (G := G) M) ≅
      FDRep.of (representationOfMonoidAlgebraModule (k := k) (G := G) N)) :
    M ≃ₗ[MonoidAlgebra k G] N :=
  letI F := forget₂ (FDRep k G) (Rep k G)
  let β := F.mapIso α
  let γ := Rep.toModuleMonoidAlgebra.mapIso β
  (asModuleRepresentationOfMonoidAlgebraModule (k := k) (G := G) M).symm ≪≫ₗ
    γ.toLinearEquiv ≪≫ₗ
      asModuleRepresentationOfMonoidAlgebraModule (k := k) (G := G) N

/-- A finite pairwise nonisomorphic family of simple group-algebra modules in the field universe
has cardinality at most the number of conjugacy classes. -/
theorem card_le_card_conjClasses_of_simpleModule_family_sameUniverse
    {ι : Type w} [Fintype ι]
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, Module.Finite k (M i)]
    [∀ i, Module (MonoidAlgebra k G) (M i)]
    [∀ i, IsScalarTower k (MonoidAlgebra k G) (M i)]
    [∀ i, IsSimpleModule (MonoidAlgebra k G) (M i)]
    (hdist : ∀ i j, Nonempty (M i ≃ₗ[MonoidAlgebra k G] M j) → i = j) :
    Fintype.card ι ≤ Fintype.card (ConjClasses G) := by
  haveI : NeZero (Nat.card G : k) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card]
    exact (isUnit_of_invertible (Fintype.card G : k)).ne_zero
  haveI hsimp_asmod : ∀ i, IsSimpleModule (MonoidAlgebra k G)
      (representationOfMonoidAlgebraModule
        (k := k) (G := G) (M i)).asModule := fun i =>
    IsSimpleModule.congr
      (asModuleRepresentationOfMonoidAlgebraModule (k := k) (G := G) (M i))
  haveI hsimp_fd : ∀ i,
      Simple (FDRep.of
        (representationOfMonoidAlgebraModule (k := k) (G := G) (M i))) := fun i =>
    inferInstance
  obtain ⟨ncc, Vcc, _hVsimp, _hVinj, hVsurj, hncc⟩ :=
    RepresentationTheory.Group.SimpleRepresentations.exists_simpleReps_card_eq_conjClasses
      (k := k) (G := G)
  choose c hc using fun i => hVsurj _ (hsimp_fd i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    refine hdist i j ?_
    obtain ⟨αi⟩ := hc i
    obtain ⟨αj⟩ := hc j
    have : Nonempty
        (FDRep.of (representationOfMonoidAlgebraModule (k := k) (G := G) (M i)) ≅
          FDRep.of
            (representationOfMonoidAlgebraModule (k := k) (G := G) (M j))) :=
      ⟨αi ≪≫ (by rw [hij]; exact αj.symm)⟩
    obtain ⟨α⟩ := this
    exact ⟨moduleLinearEquivOfFDRepIso α⟩
  calc
    Fintype.card ι ≤ Fintype.card (Fin ncc) :=
      Fintype.card_le_of_injective c hc_inj
    _ = ncc := Fintype.card_fin ncc
    _ = Fintype.card (ConjClasses G) := hncc

/-- A finite pairwise nonisomorphic family of simple group-algebra modules in any universe has
cardinality at most the number of conjugacy classes. -/
theorem card_le_card_conjClasses_of_simpleModule_family
    {ι : Type w} [Fintype ι]
    (M : ι → Type w') [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, Module.Finite k (M i)]
    [∀ i, Module (MonoidAlgebra k G) (M i)]
    [∀ i, IsScalarTower k (MonoidAlgebra k G) (M i)]
    [∀ i, IsSimpleModule (MonoidAlgebra k G) (M i)]
    (hdist : ∀ i j, Nonempty (M i ≃ₗ[MonoidAlgebra k G] M j) → i = j) :
    Fintype.card ι ≤ Fintype.card (ConjClasses G) := by
  haveI : ∀ i, Module.Free k (M i) := fun i => Module.Free.of_divisionRing k (M i)
  set N : ι → Type u := fun i => Fin (Module.finrank k (M i)) → k with hN
  let e : ∀ i, M i ≃ₗ[k] N i := fun i => (Module.finBasis k (M i)).equivFun
  letI modN : ∀ i, Module (MonoidAlgebra k G) (N i) := fun i =>
    moduleTransportAlongLinearEquiv (R := MonoidAlgebra k G) (e i)
  haveI towN : ∀ i, IsScalarTower k (MonoidAlgebra k G) (N i) := fun i =>
    isScalarTower_moduleTransportAlongLinearEquiv
      (R := MonoidAlgebra k G) (e i)
  let eR : ∀ i, M i ≃ₗ[MonoidAlgebra k G] N i := fun i =>
    linearEquiv_transportModule (R := MonoidAlgebra k G) (e i)
  haveI simpN : ∀ i, IsSimpleModule (MonoidAlgebra k G) (N i) := fun i =>
    IsSimpleModule.congr (eR i).symm
  have hdistN : ∀ i j, Nonempty (N i ≃ₗ[MonoidAlgebra k G] N j) → i = j := by
    intro i j ⟨f⟩
    exact hdist i j ⟨(eR i) ≪≫ₗ f ≪≫ₗ (eR j).symm⟩
  exact card_le_card_conjClasses_of_simpleModule_family_sameUniverse
    (k := k) (G := G) N hdistN

end Count

end RepresentationTheory.Representation.MonoidAlgebraModuleEquivalences

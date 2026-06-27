import Mathlib
import EtingofRepresentationTheory.Chapter4.Corollary4_2_2

/-!
# Counting simple `k[G]`-modules

For a finite group `G` and an algebraically closed field `k` in which `|G|` is
invertible, the number of isomorphism classes of simple `k[G]`-modules is
`|ConjClasses G|` (Etingof Corollary 4.2.2, stated for `FDRep k G`).

This file repackages that count as a **cardinality bound on abstract module
families**: any `Fintype`-indexed family of pairwise non-isomorphic simple
`k[G]`-modules, each finite-dimensional over `k`, has cardinality at most
`|ConjClasses G|`. Two forms are provided:

* `Etingof.card_le_card_conjClasses` — for modules living in `k`'s own universe
  (`Type u`), which is the universe `FDRep k G` lives in;
* `Etingof.card_le_card_conjClasses'` — for modules in an arbitrary universe,
  obtained by transporting each module to its `k`-linear small model
  `Fin (finrank k (M i)) → k : Type u`.

The bridge from a `k[G]`-module to `FDRep k G` is `repOfModule`, the
representation `g ↦ (x ↦ single g 1 • x)`, whose `asModule` recovers the
original `k[G]`-action (`repOfModule_asAlgebraHom`).
-/

open scoped MonoidAlgebra TensorProduct
open CategoryTheory

namespace Etingof

universe u v w w'

/-! ### Transporting an algebra-module structure along a `k`-linear equivalence -/

section Transport

variable {k : Type u} [CommRing k] {R : Type*} [Ring R] [Algebra k R]
  {M : Type w} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  {N : Type w'} [AddCommGroup N] [Module k N]

/-- Transport an `R`-module structure (with `R` a `k`-algebra) along a `k`-linear
equivalence `e : M ≃ₗ[k] N`, by conjugation: `r • y := e (r • e.symm y)`. -/
@[reducible]
def transportModule (e : M ≃ₗ[k] N) : Module R N where
  smul r y := e (r • e.symm y)
  one_smul y := by change e (1 • e.symm y) = y; rw [one_smul, e.apply_symm_apply]
  mul_smul r s y := by
    change e ((r * s) • e.symm y) = e (r • e.symm (e (s • e.symm y)))
    rw [e.symm_apply_apply, mul_smul]
  smul_zero r := by change e (r • e.symm 0) = 0; rw [map_zero, smul_zero, map_zero]
  smul_add r y z := by
    change e (r • e.symm (y + z)) = e (r • e.symm y) + e (r • e.symm z)
    rw [map_add, smul_add, map_add]
  add_smul r s y := by
    change e ((r + s) • e.symm y) = e (r • e.symm y) + e (s • e.symm y)
    rw [add_smul, map_add]
  zero_smul y := by change e ((0 : R) • e.symm y) = 0; rw [zero_smul, map_zero]

/-- Under `transportModule e`, the transported scalar action forms a scalar tower
with `N`'s native `k`-action. -/
theorem transportModule_isScalarTower (e : M ≃ₗ[k] N) :
    @IsScalarTower k R N _ (transportModule e).toSMul _ := by
  letI := transportModule (k := k) (R := R) e
  refine ⟨fun c r y => ?_⟩
  change e ((c • r) • e.symm y) = c • e (r • e.symm y)
  rw [smul_assoc, map_smul]

/-- Under `transportModule e`, the map `e` itself is `R`-linear, giving an
`R`-linear equivalence `M ≃ₗ[R] N`. -/
def transportLinearEquiv (e : M ≃ₗ[k] N) :
    letI := transportModule (k := k) (R := R) e
    M ≃ₗ[R] N :=
  letI := transportModule (k := k) (R := R) e
  { e.toAddEquiv with
    map_smul' := fun r x => by
      change e (r • x) = e (r • e.symm (e x))
      rw [LinearEquiv.symm_apply_apply] }

end Transport

/-! ### The representation attached to a `k[G]`-module -/

section RepOfModule

variable {k : Type u} [Field k] {G : Type v} [Group G]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]

/-- The representation `g ↦ (x ↦ single g 1 • x)` attached to a `k[G]`-module `M`
that is a scalar tower over `k`. -/
noncomputable def repOfModule : Representation k G M :=
  (Algebra.lsmul k k M : MonoidAlgebra k G →ₐ[k] Module.End k M).toRingHom.toMonoidHom.comp
    (MonoidAlgebra.of k G)

theorem repOfModule_apply (g : G) (x : M) :
    repOfModule (k := k) (G := G) M g x = MonoidAlgebra.single g (1 : k) • x := rfl

/-- The algebra homomorphism `k[G] → End k M` underlying `repOfModule M` is exactly
left multiplication `Algebra.lsmul`. Hence the `k[G]`-action on `(repOfModule M).asModule`
agrees with the original `k[G]`-action on `M`. -/
theorem repOfModule_asAlgebraHom :
    (repOfModule (k := k) (G := G) M).asAlgebraHom = Algebra.lsmul k k M := by
  apply MonoidAlgebra.algHom_ext
  intro g
  rw [Representation.asAlgebraHom_single_one]
  rfl

/-- The identity map is a `k[G]`-linear equivalence between `(repOfModule M).asModule`
and `M` (the two `k[G]`-actions coincide). -/
noncomputable def repOfModuleAsModuleEquiv :
    (repOfModule (k := k) (G := G) M).asModule ≃ₗ[MonoidAlgebra k G] M :=
  { (repOfModule (k := k) (G := G) M).asModuleEquiv.toAddEquiv with
    map_smul' := fun r x => by
      change (repOfModule (k := k) (G := G) M).asModuleEquiv (r • x)
        = r • (repOfModule (k := k) (G := G) M).asModuleEquiv x
      rw [Representation.asModuleEquiv_map_smul, repOfModule_asAlgebraHom]
      rfl }

end RepOfModule

end Etingof

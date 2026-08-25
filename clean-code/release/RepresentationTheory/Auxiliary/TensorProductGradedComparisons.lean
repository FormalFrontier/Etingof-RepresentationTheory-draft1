/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses
import RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolutionComplexComparison
import RepresentationTheory.LinearYonedaTensorProductComparison
import RepresentationTheory.Algebra.Homology.TensorResolution
import RepresentationTheory.HomologicalAlgebra.TensorProduct
import RepresentationTheory.Algebra.Homology.LinearYoneda
import RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity
import RepresentationTheory.Algebra.Homology.TensorBarResolution
import RepresentationTheory.ModuleCat.RightTensor
import RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing
import RepresentationTheory.HomologicalComplex.TensorExtension
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import RepresentationTheory.Alignment.Attribute

/-!
# Problem 8.2.8: Künneth formula for `Tor` and `Ext` over a tensor product of algebras

If `A₁, A₂` are algebras over a field `k`, and `Mᵢ, Nᵢ` are `Aᵢ`-modules, then

* `Torᵢ^{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Torⱼ^{A₁}(M₁, N₁) ⊗ₖ Torₘ^{A₂}(M₂, N₂)`,
* `Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`
  when the `Aᵢ`, `Mᵢ` and `Nᵢ` are all finite dimensional over `k` (the `Mᵢ`-finiteness is what
  lets the resolving `Pᵢ` be finitely generated projective; see `Auxiliary.nonempty_tensorProductGradedPieceLinearEquivDirectSum`).

All tensor products of the factor `Tor`/`Ext` on the right-hand side are over the **field `k`**, as
in the book: the objects are `k`-vector spaces and the Künneth summands are their `k`-linear tensor
products, not the (much larger) group-level `⊗_ℤ`.

## What is formalized here

Both the `Tor` and `Ext` statements are proved below. The `Ext` statement
(`Auxiliary.nonempty_tensorProductGradedPieceLinearEquivDirectSum`) is assembled from its `k`-linear core `Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma`, the comparison
isomorphism `RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity.projectiveResolutionDegreeLinearEquiv` (`RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses ≃ₗ[k] RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology`), the finitely generated projective
`RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution`, and the coproduct-to-direct-sum identification (`ModuleCat.coprodIsoDirectSum`).
The `hXM` object identification (the factor `k`-module-diamond reconciliation that identifies the
statement's `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)` with the canonical `RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct`) is
discharged inside the proof by `subst`ing the ambient `Module k Mᵢ` with its restricted form and
then `Auxiliary.tensorProductModule_eq_of_smul_tmul` (see the comment there).

### The external tensor product module structures

The theorem's content lives in three tensor products of `k`-vector spaces: `A₁ ⊗ₖ A₂` (a
`k`-algebra, via `Algebra.TensorProduct`), `M₁ ⊗ₖ M₂`, and `N₁ ⊗ₖ N₂`. The key structures are:

* `N₁ ⊗ₖ N₂` is a **left** `A₁ ⊗ₖ A₂`-module with `(a₁ ⊗ a₂) • (n₁ ⊗ n₂) = (a₁ • n₁) ⊗ (a₂ • n₂)`;
* for `Tor`, `M₁ ⊗ₖ M₂` is a **right** `A₁ ⊗ₖ A₂`-module (i.e. a left `(A₁ ⊗ₖ A₂)ᵐᵒᵖ`-module) with
  `(m₁ ⊗ m₂) · (a₁ ⊗ a₂) = (m₁ · a₁) ⊗ (m₂ · a₂)`;
* for `Ext`, `M₁ ⊗ₖ M₂` is a **left** `A₁ ⊗ₖ A₂`-module, componentwise as for `N`.

For the `Tor` statement, the right external module on `M₁ ⊗ₖ M₂` is realised by the actual
construction `RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject` (from `RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.moduleOppositeTensorProduct`), whose componentwise
action is `RepresentationTheory.Algebra.TensorProduct.OppositeModule.TensorProduct.op_tmul_smul_tmul`. The left external module on `N₁ ⊗ₖ N₂` is taken as
a parameter `instN` pinned to act componentwise on simple tensors by `hN`; because simple tensors
generate the tensor product and the action is additive, this determines it uniquely as the canonical
external tensor product, and it is the structure the rearrangement machinery
(`RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolutionComplexComparison.mappedComplexIsoTensorMappedProjectiveResolutionComplexes`) consumes.

### The right-hand side

`Torⱼ^{A₁}(M₁, N₁)` as a `k`-vector space is `RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k A₁ N₁ M₁ j : ModuleCat k` (the
`k`-linear left derived functor of `- ⊗_{A₁} N₁`, refining the `AddCommGrpCat`-valued
`RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup`). The Künneth summands `Torⱼ^{A₁}(M₁, N₁) ⊗ₖ Torₘ^{A₂}(M₂, N₂)` are their monoidal
tensor products in
`ModuleCat k`, and `⨁_{j+m=i}` is the coproduct `∐` over `{p : ℕ × ℕ // p.1 + p.2 = i}` in
`ModuleCat k`. For `Ext`, whose values carry no such `k`-linear derived-functor refinement here, the
summands are the `k`-linear tensor products `TensorProduct k` of the underlying `Ext` groups, which
are `k`-modules through the `Linear k (ModuleCat A)` structure of a module category over a
`k`-algebra.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct DirectSum

namespace RepresentationTheory.Auxiliary.TensorProductGradedComparisons

universe u

section Tor

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
-- right `Aᵢ`-modules `Mᵢ` (`ModuleCat Aᵢᵐᵒᵖ`)
variable (M₁ : ModuleCat.{u} A₁ᵐᵒᵖ) (M₂ : ModuleCat.{u} A₂ᵐᵒᵖ)
-- left `Aᵢ`-modules `Nᵢ`, `k`-linearly (`IsScalarTower k Aᵢ Nᵢ`)
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]

/-- Constructs the degreewise isomorphism for opposite-side module objects from the tensor-product construction to the indexed sum of the two component constructions. -/
noncomputable def Auxiliary.rightModuleTensorProductObjectIsoSigma (i : ℕ)
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂) i
      ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
          RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k A₁ N₁ M₁ p.1.1 ⊗ RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k A₂ N₂ M₂ p.1.2 :=
  -- Chosen projective resolutions of the two right modules, and of their external tensor.
  let P₁ : ProjectiveResolution M₁ := ProjectiveResolution.of M₁
  let P₂ : ProjectiveResolution M₂ := ProjectiveResolution.of M₂
  let Q : ProjectiveResolution (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂) :=
    RepresentationTheory.Algebra.Homology.TensorResolution.tensorProjectiveResolution P₁ P₂
  -- The two `k`-linear factor complexes `Cᵢ = P•ᵢ ⊗_{Aᵢ} Nᵢ`.
  -- Step 1: `Torᵢ` of the external tensor = `Hᵢ` of `(P•₁ ⊗_k P•₂) ⊗_{A₁⊗A₂} (N₁⊗ₖN₂)`.
  RepresentationTheory.ModuleCat.RightTensor.rightTensorProjectiveResolutionHomologyIso k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)
      (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂) Q i ≪≫
  -- Step 2 & 3: rearrange the complex to `(P•₁ ⊗_{A₁} N₁) ⊗_k (P•₂ ⊗_{A₂} N₂)`, then take `Hᵢ`.
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
      (RepresentationTheory.HomologicalAlgebra.TensorProduct.ProjectiveResolutionComplexComparison.mappedComplexIsoTensorMappedProjectiveResolutionComplexes k A₁ A₂ N₁ N₂ hN P₁ P₂) ≪≫
  -- Step 4a: algebraic Künneth over the field for the tensor of the two factor complexes.
  RepresentationTheory.HomologicalComplex.TensorProduct.Reindexing.homologyTensorIsoSigma
      (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₁ N₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex)
      (((RepresentationTheory.ModuleCat.RightTensor.rightTensorFunctor k A₂ N₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₂.complex)
      i ≪≫
  -- Step 4b: identify the factor homologies as `Torⱼ^{A₁}` / `Torₘ^{A₂}`.
  Sigma.mapIso (fun p => tensorIso
    (RepresentationTheory.ModuleCat.RightTensor.rightTensorProjectiveResolutionHomologyIso k A₁ N₁ M₁ P₁ p.1.1).symm
    (RepresentationTheory.ModuleCat.RightTensor.rightTensorProjectiveResolutionHomologyIso k A₂ N₂ M₂ P₂ p.1.2).symm)

/-- For opposite-side module objects and a componentwise scalar action on pure tensors, asserts the existence of a degreewise isomorphism with the indexed sum over complementary degrees. -/
@[source_ref "Chapter8/Problem8.2.8" (role := supporting)]
theorem Auxiliary.nonempty_rightModuleTensorProductObjectIsoSigma (i : ℕ)
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Nonempty
      (RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂) i
        ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
            RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k A₁ N₁ M₁ p.1.1 ⊗ RepresentationTheory.ModuleCat.RightTensor.auxiliaryIndexedModuleFunctorObj k A₂ N₂ M₂ p.1.2) :=
  ⟨Auxiliary.rightModuleTensorProductObjectIsoSigma k A₁ A₂ M₁ M₂ N₁ N₂ i hN⟩

end Tor

section Ext

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
  [FiniteDimensional k A₁] [FiniteDimensional k A₂]
-- left `Aᵢ`-modules `Mᵢ`, `Nᵢ`; the `Mᵢ` and `Nᵢ` are finite dimensional over `k`.
-- Finite dimensionality of the `Mᵢ` is what lets their projective resolutions be chosen
-- finitely generated projective, which is exactly what makes the degreewise Hom-tensor
-- map an isomorphism; the `Nᵢ` finiteness matches the book text.
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [FiniteDimensional k M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [FiniteDimensional k M₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [FiniteDimensional k N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [FiniteDimensional k N₂]

/-- Shows that a module structure on a tensor product whose action on pure tensors is componentwise agrees with the displayed tensor-product module structure. -/
theorem Auxiliary.tensorProductModule_eq_of_smul_tmul
    {k : Type u} [Field k] {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
    {M₁ M₂ : Type u}
    [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [IsScalarTower k A₁ M₁]
    [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [IsScalarTower k A₂ M₂]
    (instM : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂))
    (hM : ∀ (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂),
      (haveI := instM; (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : M₁ ⊗[k] M₂))
        = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂)) :
    instM = RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k A₁ A₂ M₁ M₂ := by
  refine Module.ext' instM (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule k A₁ A₂ M₁ M₂) fun r x => ?_
  -- The target smul `(RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule …).smul r x` is *definitionally* the representation
  -- `RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom … r` applied to `x` (the canonical structure is `Module.compHom` of that
  -- algebra map). Rewriting the goal into that explicit-linear-map form removes the second
  -- `Module` instance, so plain `rw` on the source `instM` side and `map_add`/`map_zero` on the
  -- representation side suffice.
  change (haveI := instM; r • x) = RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom k A₁ A₂ M₁ M₂ r x
  induction r using TensorProduct.induction_on with
  | zero => rw [zero_smul, map_zero, LinearMap.zero_apply]
  | tmul a₁ a₂ =>
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero]
    | tmul m₁ m₂ =>
      rw [hM a₁ a₂ m₁ m₂]
      exact (RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.smul_tmul k A₁ A₂ M₁ M₂ a₁ a₂ m₁ m₂).symm
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  | add r r' hr hr' => rw [add_smul, map_add, LinearMap.add_apply, hr, hr']

/-- Builds a scalar tower from a tensor-product module action that distributes componentwise over pure tensors. -/
theorem Auxiliary.tensorProductIsScalarTower_of_smul_tmul
    {k : Type u} [Field k] {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
    {M₁ M₂ : Type u}
    [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [IsScalarTower k A₁ M₁]
    [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [IsScalarTower k A₂ M₂]
    (instM : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂))
    (hM : ∀ (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂),
      (haveI := instM; (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : M₁ ⊗[k] M₂))
        = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂)) :
    letI := instM
    IsScalarTower k (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) := by
  letI := instM
  refine ⟨fun c r m => ?_⟩
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a₁ a₂ =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul m₁ m₂ =>
      rw [show (c • (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) = (c • a₁) ⊗ₜ[k] a₂ from
            TensorProduct.smul_tmul' c a₁ a₂,
          hM, hM, smul_assoc, TensorProduct.smul_tmul' c (a₁ • m₁) (a₂ • m₂)]
    | add x y hx hy => simp only [smul_add, hx, hy]
  | add r r' hr hr' => simp only [add_smul, smul_add, hr, hr']

/-- Constructs the degreewise isomorphism between the object over the tensor-product algebra and the indexed sum of tensor products of the two resolution-based objects. -/
noncomputable def Auxiliary.projectiveResolutionTensorProductObjectIsoSigma (i : ℕ)
    (P₁ : ProjectiveResolution (ModuleCat.of A₁ M₁))
    (P₂ : ProjectiveResolution (ModuleCat.of A₂ M₂))
    [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
    [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]
    [IsScalarTower k A₁ N₁] [IsScalarTower k A₂ N₂]
    [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k (A₁ ⊗[k] A₂)
        (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ (ModuleCat.of A₁ M₁) (ModuleCat.of A₂ M₂))
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) i
      ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
          RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k A₁ (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1
            ⊗ RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k A₂ (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2 :=
    -- Step 1: `Extⁱ` of the external tensor = `Hⁱ` of `Hom_{A₁⊗A₂}(P•₁ ⊗ₖ P•₂, N₁⊗ₖN₂)`.
    RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution k (A₁ ⊗[k] A₂) _
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) (RepresentationTheory.HomologicalAlgebra.TensorProduct.tensorProduct P₁ P₂) i ≪≫
    -- Step 2 & 3: rearrange to `Hom_{A₁}(P•₁,N₁) ⊗ₖ Hom_{A₂}(P•₂,N₂)`, then take `Hⁱ`.
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i).mapIso
        (RepresentationTheory.LinearYonedaTensorProductComparison.linearYonedaTensorProductComplexIso k N₁ N₂ hN P₁ P₂) ≪≫
    -- Step 4a: cochain Künneth over the field for the tensor of the two Hom complexes.
    RepresentationTheory.HomologicalComplex.TensorExtension.homologyTensorIsoSigma
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) i ≪≫
    -- Step 4b: identify the factor cohomologies as `Extⱼ^{A₁}` / `Extₘ^{A₂}`.
    Sigma.mapIso (fun p => tensorIso
      (RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution k A₁ (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) P₁ p.1.1).symm
      (RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomologyIsoOfProjectiveResolution k A₂ (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) P₂ p.1.2).symm)

/-- Under finite projective resolution hypotheses and compatibility of scalar multiplication on pure tensors, asserts the existence of a degreewise isomorphism with the indexed sum of tensor products in complementary degrees. -/
@[source_ref "Chapter8/Problem8.2.8" (role := supporting)]
theorem Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma (i : ℕ)
    (P₁ : ProjectiveResolution (ModuleCat.of A₁ M₁))
    (P₂ : ProjectiveResolution (ModuleCat.of A₂ M₂))
    [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
    [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]
    [IsScalarTower k A₁ N₁] [IsScalarTower k A₂ N₂]
    [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Nonempty
      (RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k (A₁ ⊗[k] A₂)
          (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ (ModuleCat.of A₁ M₁) (ModuleCat.of A₂ M₂))
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) i
        ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
            RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k A₁ (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1
              ⊗ RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k A₂ (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2) :=
  ⟨Auxiliary.projectiveResolutionTensorProductObjectIsoSigma k A₁ A₂ M₁ M₂ N₁ N₂ i P₁ P₂ hN⟩

-- The factor `k`-scalar towers on `Mᵢ` / `Nᵢ`: needed to form the finitely generated projective
-- `RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution` and consumed by `Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma`. They only attach to
-- `Auxiliary.nonempty_tensorProductGradedPieceLinearEquivDirectSum` below (not to `Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma`, which lists its `Nᵢ` towers explicitly).
variable [IsScalarTower k A₁ M₁] [IsScalarTower k A₂ M₂]
  [IsScalarTower k A₁ N₁] [IsScalarTower k A₂ N₂]

/-- Under componentwise scalar-action hypotheses, asserts the existence of a linear equivalence between the degree-indexed tensor-product object and the direct sum of tensor products indexed by pairs whose degrees add to the chosen index. -/
@[source_ref "Chapter8/Problem8.2.8" (role := supporting)]
theorem Auxiliary.nonempty_tensorProductGradedPieceLinearEquivDirectSum (i : ℕ)
    [instM : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)]
    [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    (hM : ∀ (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : M₁ ⊗[k] M₂)
        = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Nonempty
      (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂))
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) i
        ≃ₗ[k] (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = i},
              TensorProduct k
                (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1)
                (RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2))) := by
  -- The `k`-linear Künneth isomorphism `Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma` is the mathematical core: it decomposes
  -- `RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k (A₁⊗A₂) (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct…) (N₁⊗N₂) i` as the categorical coproduct
  -- `∐_{j+m=i} RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k A₁ M₁ N₁ j ⊗ RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology k A₂ M₂ N₂ m` in `ModuleCat k`. The proof combines it via:
  --   1. `RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution` (finitely generated projective, `RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution_complex_finite`
  --      + `RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarTerm_projective`) resolves each `Mᵢ` and the external `M₁⊗M₂`; the tensor scalar
  --      towers come from `Auxiliary.tensorProductIsScalarTower_of_smul_tmul`.
  --   2. `Auxiliary.tensorProductModule_eq_of_smul_tmul` identifies the statement's `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)`
  --      (pinned by `hM`) with the canonical `RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct` (`hXM`); `instN`/`hN` are
  --      passed to `Auxiliary.nonempty_projectiveResolutionTensorProductObjectIsoSigma` directly on the `N` side.
  --   3. the comparison `RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity.projectiveResolutionDegreeLinearEquiv` (`RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses ≃ₗ[k] RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology`) transports the big `Ext` and,
  --      backwards under `TensorProduct.congr`, each factor `RepresentationTheory.Algebra.Homology.LinearYoneda.ModuleCat.linearYonedaHomology` summand.
  --   4. `ModuleCat.coprodIsoDirectSum` turns `∐` into `⨁`; the monoidal `⊗` in `ModuleCat k` is
  --      definitionally `TensorProduct k`, so `DirectSum.congrLinearEquiv` finishes.
  haveI : IsScalarTower k (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) := Auxiliary.tensorProductIsScalarTower_of_smul_tmul instM hM
  haveI : IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) := Auxiliary.tensorProductIsScalarTower_of_smul_tmul instN hN
  have hXM : (ModuleCat.of (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) : ModuleCat.{u} (A₁ ⊗[k] A₂))
      = RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ (ModuleCat.of A₁ M₁) (ModuleCat.of A₂ M₂) := by
    -- **Object identification.** The two objects both have carrier
    -- `M₁ ⊗[k] M₂` and act componentwise, but they are not *definitionally* equal:
    -- `RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct` bakes in `RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux` (the `k`-structure on each factor
    -- obtained by restricting the `Aᵢ`-action along `k → Aᵢ`), whereas the statement's
    -- `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)` carries the ambient `Module k Mᵢ`. These agree by
    -- `IsScalarTower k Aᵢ Mᵢ`, but reconciling the two `k`-structures (carried through
    -- `RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule` / `RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.moduleEndAlgHom`) is a self-contained module reconciliation.
    -- The factor identification is `RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier`/`RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux`
    -- (`= Module.compHom _ (algebraMap k Aᵢ)`) vs the ambient `Module k Mᵢ`, equal by
    -- `IsScalarTower.algebraMap_smul`. We reconcile by `subst`ing the ambient `Module k Mᵢ` with
    -- its restricted form `Module.compHom Mᵢ (algebraMap k Aᵢ)` (equal via `Module.ext'`), which
    -- makes the carriers `M₁ ⊗[k] M₂` definitionally equal. The residual `A₁⊗A₂`-action agreement
    -- is then `Auxiliary.tensorProductModule_eq_of_smul_tmul`.
    have e1 : (inferInstance : Module k M₁) = Module.compHom M₁ (algebraMap k A₁) :=
      Module.ext' _ _ fun c m => (IsScalarTower.algebraMap_smul (A := A₁) c m).symm
    have e2 : (inferInstance : Module k M₂) = Module.compHom M₂ (algebraMap k A₂) :=
      Module.ext' _ _ fun c m => (IsScalarTower.algebraMap_smul (A := A₂) c m).symm
    subst e1 e2
    -- `subst` eliminated the ambient `Module k Mᵢ` instance binders; re-register the (now
    -- identical) restricted forms so typeclass resolution can supply
    -- `Auxiliary.tensorProductModule_eq_of_smul_tmul`. `letI` (not `haveI`) keeps the binding transparent, so
    -- the synthesized instance is *definitionally* the `Module.compHom Mᵢ (algebraMap k Aᵢ)` that
    -- `subst` baked into `instM`'s carrier type.
    letI : Module k M₁ := Module.compHom M₁ (algebraMap k A₁)
    letI : Module k M₂ := Module.compHom M₂ (algebraMap k A₂)
    rw [Auxiliary.tensorProductModule_eq_of_smul_tmul instM hM]
    -- Both sides are now `ModuleCat.of (A₁⊗A₂) (M₁ ⊗[k] M₂)` with the `RepresentationTheory.Algebra.TensorProduct.Module.TensorProduct.instModule`
    -- action over the restricted factor `k`-structures, to which `RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct` unfolds.
    rfl
  refine ⟨?_⟩
  refine (RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity.projectiveResolutionDegreeLinearEquiv k (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))
      (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)) i) ≪≫ₗ ?_
  rw [hXM]
  refine (Auxiliary.projectiveResolutionTensorProductObjectIsoSigma k A₁ A₂ M₁ M₂ N₁ N₂ i
      (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A₁ M₁) (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A₂ M₂) hN).toLinearEquiv ≪≫ₗ ?_
  refine (ModuleCat.coprodIsoDirectSum _).toLinearEquiv ≪≫ₗ ?_
  exact DirectSum.congrLinearEquiv (fun p => TensorProduct.congr
    (RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity.projectiveResolutionDegreeLinearEquiv k (ModuleCat.of A₁ N₁) (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A₁ M₁) p.1.1).symm
    (RepresentationTheory.Algebra.HomologicalComplex.HomologyLinearity.projectiveResolutionDegreeLinearEquiv k (ModuleCat.of A₂ N₂) (RepresentationTheory.Algebra.Homology.TensorBarResolution.tensorBarResolution k A₂ M₂) p.1.2).symm)

end Ext

end RepresentationTheory.Auxiliary.TensorProductGradedComparisons

import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import EtingofRepresentationTheory.Chapter8.RearrangeComplex
import EtingofRepresentationTheory.Chapter8.RearrangeHomComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorResolution
import EtingofRepresentationTheory.Chapter8.ExternalTensorResolutionLeft
import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
import EtingofRepresentationTheory.Chapter8.ExtAbelianComparison
import EtingofRepresentationTheory.Chapter8.BarResolution
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat
import EtingofRepresentationTheory.Chapter7.KunnethCochainComplexNat
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Problem 8.2.8: Künneth formula for `Tor` and `Ext` over a tensor product of algebras

If `A₁, A₂` are algebras over a field `k`, and `Mᵢ, Nᵢ` are `Aᵢ`-modules, then

* `Torᵢ^{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Torⱼ^{A₁}(M₁, N₁) ⊗ₖ Torₘ^{A₂}(M₂, N₂)`,
* `Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`
  when the `Aᵢ`, `Mᵢ` and `Nᵢ` are all finite dimensional over `k` (the `Mᵢ`-finiteness is what
  lets the resolving `Pᵢ` be finitely generated projective; see `Problem_8_2_8_ext`).

All tensor products of the factor `Tor`/`Ext` on the right-hand side are over the **field `k`**, as
in the book: the objects are `k`-vector spaces and the Künneth summands are their `k`-linear tensor
products, not the (much larger) group-level `⊗_ℤ`.

## What is formalized here

Both the `Tor` and `Ext` statements are proved below. The `Ext` statement
(`Problem_8_2_8_ext`) is assembled from its `k`-linear core `Problem_8_2_8_extₖ`, the comparison
isomorphism `extAbelianIsoExtₖ` (`Etingof.Ext ≃ₗ[k] Extₖ`), the finitely generated projective
`barResolution`, and the coproduct-to-direct-sum identification (`ModuleCat.coprodIsoDirectSum`).
The `hXM` object identification (the factor `k`-module-diamond reconciliation that identifies the
statement's `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)` with the canonical `extTensorFunctorLeftObj`) is
discharged inside the proof by `subst`ing the ambient `Module k Mᵢ` with its restricted form and
then `instModule_eq_extTensorModuleLeft` (see the comment there).

### The external tensor product module structures

The theorem's content lives in three tensor products of `k`-vector spaces: `A₁ ⊗ₖ A₂` (a
`k`-algebra, via `Algebra.TensorProduct`), `M₁ ⊗ₖ M₂`, and `N₁ ⊗ₖ N₂`. The key structures are:

* `N₁ ⊗ₖ N₂` is a **left** `A₁ ⊗ₖ A₂`-module with `(a₁ ⊗ a₂) • (n₁ ⊗ n₂) = (a₁ • n₁) ⊗ (a₂ • n₂)`;
* for `Tor`, `M₁ ⊗ₖ M₂` is a **right** `A₁ ⊗ₖ A₂`-module (i.e. a left `(A₁ ⊗ₖ A₂)ᵐᵒᵖ`-module) with
  `(m₁ ⊗ m₂) · (a₁ ⊗ a₂) = (m₁ · a₁) ⊗ (m₂ · a₂)`;
* for `Ext`, `M₁ ⊗ₖ M₂` is a **left** `A₁ ⊗ₖ A₂`-module, componentwise as for `N`.

For the `Tor` statement, the right external module on `M₁ ⊗ₖ M₂` is realised by the actual
construction `Etingof.extTensorFunctorObj` (from `Etingof.extTensorModule`), whose componentwise
action is `Etingof.extTensorModule_op_smul_tmul`. The left external module on `N₁ ⊗ₖ N₂` is taken as
a parameter `instN` pinned to act componentwise on simple tensors by `hN`; because simple tensors
generate the tensor product and the action is additive, this determines it uniquely as the canonical
external tensor product, and it is the structure the rearrangement machinery
(`Etingof.rearrangeComplex`) consumes.

### The right-hand side

`Torⱼ^{A₁}(M₁, N₁)` as a `k`-vector space is `Etingof.Torₖ k A₁ N₁ M₁ j : ModuleCat k` (the
`k`-linear left derived functor of `- ⊗_{A₁} N₁`, refining the `AddCommGrpCat`-valued
`Etingof.Tor`). The Künneth summands `Torⱼ^{A₁}(M₁, N₁) ⊗ₖ Torₘ^{A₂}(M₂, N₂)` are their monoidal
tensor products in
`ModuleCat k`, and `⨁_{j+m=i}` is the coproduct `∐` over `{p : ℕ × ℕ // p.1 + p.2 = i}` in
`ModuleCat k`. For `Ext`, whose values carry no such `k`-linear derived-functor refinement here, the
summands are the `k`-linear tensor products `TensorProduct k` of the underlying `Ext` groups, which
are `k`-modules through the `Linear k (ModuleCat A)` structure of a module category over a
`k`-algebra.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct DirectSum

namespace Etingof

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

/-- **Problem 8.2.8, `Tor`.** For `k`-algebras `A₁, A₂`, right modules `M₁, M₂` and left modules
`N₁, N₂`, the `Tor` of the external tensor products decomposes as a Künneth direct sum over the
field `k`:
`Torᵢ^{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) ≅ ⨁_{j+m=i} Torⱼ^{A₁}(M₁, N₁) ⊗ₖ Torₘ^{A₂}(M₂, N₂)`.

The right external `(A₁ ⊗ A₂)ᵐᵒᵖ`-module on `M₁ ⊗ₖ M₂` is `Etingof.extTensorFunctorObj`; the left
external `A₁ ⊗ A₂`-module on `N₁ ⊗ₖ N₂` is `instN`, pinned by `hN` to act componentwise on simple
tensors.

The proof is the four-step book route: a tensor of projective resolutions
(`extTensorProjectiveResolution`), the complex-level rearrangement `rearrangeComplex`, and the
algebraic Künneth theorem over the field `kunnethChainComplexNatIso`, with the factor homologies
identified as `Torₖ` through `torIsoHomologyTensorRightₖ`. -/
noncomputable def Problem_8_2_8_torIso (i : ℕ)
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Torₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (extTensorFunctorObj k A₁ A₂ M₁ M₂) i
      ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
          Torₖ k A₁ N₁ M₁ p.1.1 ⊗ Torₖ k A₂ N₂ M₂ p.1.2 :=
  -- Chosen projective resolutions of the two right modules, and of their external tensor.
  let P₁ : ProjectiveResolution M₁ := ProjectiveResolution.of M₁
  let P₂ : ProjectiveResolution M₂ := ProjectiveResolution.of M₂
  let Q : ProjectiveResolution (extTensorFunctorObj k A₁ A₂ M₁ M₂) :=
    extTensorProjectiveResolution P₁ P₂
  -- The two `k`-linear factor complexes `Cᵢ = P•ᵢ ⊗_{Aᵢ} Nᵢ`.
  -- Step 1: `Torᵢ` of the external tensor = `Hᵢ` of `(P•₁ ⊗_k P•₂) ⊗_{A₁⊗A₂} (N₁⊗ₖN₂)`.
  torIsoHomologyTensorRightₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)
      (extTensorFunctorObj k A₁ A₂ M₁ M₂) Q i ≪≫
  -- Step 2 & 3: rearrange the complex to `(P•₁ ⊗_{A₁} N₁) ⊗_k (P•₂ ⊗_{A₂} N₂)`, then take `Hᵢ`.
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
      (rearrangeComplex k A₁ A₂ N₁ N₂ hN P₁ P₂) ≪≫
  -- Step 4a: algebraic Künneth over the field for the tensor of the two factor complexes.
  kunnethChainComplexNatIso
      (((tensorRightFunctorₖ k A₁ N₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex)
      (((tensorRightFunctorₖ k A₂ N₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₂.complex)
      i ≪≫
  -- Step 4b: identify the factor homologies as `Torⱼ^{A₁}` / `Torₘ^{A₂}`.
  Sigma.mapIso (fun p => tensorIso
    (torIsoHomologyTensorRightₖ k A₁ N₁ M₁ P₁ p.1.1).symm
    (torIsoHomologyTensorRightₖ k A₂ N₂ M₂ P₂ p.1.2).symm)

/-- **Problem 8.2.8, `Tor`**, `Nonempty` form: a one-line corollary of the isomorphism
`Problem_8_2_8_torIso`, kept for consumers phrased in terms of `Nonempty`. -/
theorem Problem_8_2_8_tor (i : ℕ)
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Nonempty
      (Torₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (extTensorFunctorObj k A₁ A₂ M₁ M₂) i
        ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
            Torₖ k A₁ N₁ M₁ p.1.1 ⊗ Torₖ k A₂ N₂ M₂ p.1.2) :=
  ⟨Problem_8_2_8_torIso k A₁ A₂ M₁ M₂ N₁ N₂ i hN⟩

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

/-- **Module-structure reconciliation.** An abstract left
`A₁ ⊗[k] A₂`-module structure `instM` on `M₁ ⊗[k] M₂` that acts componentwise on simple tensors
(`hM`) *is* the canonical external structure `Etingof.extTensorModuleLeft`. Both actions are additive
in each argument and simple tensors span `A₁ ⊗[k] A₂` and `M₁ ⊗[k] M₂`, so agreeing on
`(a₁ ⊗ a₂) • (m₁ ⊗ m₂)` forces them equal as `Module` structures (via `Module.ext'`).

This is what lets `Problem_8_2_8_ext` identify its statement's `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)`
(carrying `instM`, pinned by `hM`) with the `extTensorFunctorLeftObj` consumed by
`Problem_8_2_8_extₖ`. -/
theorem instModule_eq_extTensorModuleLeft
    {k : Type u} [Field k] {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
    {M₁ M₂ : Type u}
    [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [IsScalarTower k A₁ M₁]
    [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [IsScalarTower k A₂ M₂]
    (instM : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂))
    (hM : ∀ (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂),
      (haveI := instM; (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : M₁ ⊗[k] M₂))
        = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂)) :
    instM = extTensorModuleLeft k A₁ A₂ M₁ M₂ := by
  refine Module.ext' instM (extTensorModuleLeft k A₁ A₂ M₁ M₂) fun r x => ?_
  -- The target smul `(extTensorModuleLeft …).smul r x` is *definitionally* the representation
  -- `extTensorRepLeft … r` applied to `x` (the canonical structure is `Module.compHom` of that
  -- algebra map). Rewriting the goal into that explicit-linear-map form removes the second
  -- `Module` instance, so plain `rw` on the source `instM` side and `map_add`/`map_zero` on the
  -- representation side suffice.
  change (haveI := instM; r • x) = extTensorRepLeft k A₁ A₂ M₁ M₂ r x
  induction r using TensorProduct.induction_on with
  | zero => rw [zero_smul, map_zero, LinearMap.zero_apply]
  | tmul a₁ a₂ =>
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero]
    | tmul m₁ m₂ =>
      rw [hM a₁ a₂ m₁ m₂]
      exact (extTensorModuleLeft_smul_tmul k A₁ A₂ M₁ M₂ a₁ a₂ m₁ m₂).symm
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  | add r r' hr hr' => rw [add_smul, map_add, LinearMap.add_apply, hr, hr']

/-- **`k`-`(A₁ ⊗ A₂)`-scalar tower for a componentwise external module.** An
abstract left `A₁ ⊗[k] A₂`-module structure `instM` on `M₁ ⊗[k] M₂` acting componentwise on simple
tensors (`hM`) is automatically a `k`-scalar tower: `(c • r) • x = c • (r • x)`. Both sides are
additive in `r` and `x`, so it reduces to simple tensors, where `c • (a₁ ⊗ a₂) = (c • a₁) ⊗ a₂`
(`TensorProduct.smul_tmul'`) and the factor scalar towers `IsScalarTower k Aᵢ Mᵢ` finish it. This
supplies the `IsScalarTower k (A₁ ⊗ A₂) (M₁ ⊗ M₂)` / `(N₁ ⊗ N₂)` instances that `barResolution` and
`Problem_8_2_8_extₖ` demand of the statement's pinned `instM` / `instN` in `Problem_8_2_8_ext`. -/
theorem isScalarTower_extTensor
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

/-- **Problem 8.2.8, `Ext`: the `k`-linear (`Extₖ`) Künneth isomorphism.** The cohomological
mirror of `Problem_8_2_8_tor`, phrased with the `ModuleCat k`-valued left-derived-functor `Extₖ`
and consuming finitely generated projective resolutions `P₁, P₂` of the two left factor modules.

The proof is the four-step book route dualised through `Hom`:
1. `Extⁱ_{A₁⊗A₂}(M₁⊗M₂, N₁⊗N₂) ≅ Hⁱ(Hom_{A₁⊗A₂}(P•₁ ⊗ₖ P•₂, N₁⊗N₂))` via `extIsoCohomologyHomₖ`
   with `P•₁ ⊗ₖ P•₂ = extTensorProjectiveResolutionLeft P₁ P₂`;
2. rearrange the Hom cochain complex to `Hom_{A₁}(P•₁, N₁) ⊗ₖ Hom_{A₂}(P•₂, N₂)`
   (`rearrangeHomComplex`, needs the `Pᵢ` finitely generated projective), then take `Hⁱ`;
3. cochain Künneth over `k` (`kunnethCochainComplexNatIso`);
4. identify the factor cohomologies as `Extⱼ^{A₁}` / `Extₘ^{A₂}` (`extIsoCohomologyHomₖ` again).

The finite-generation of the `Pᵢ` (an `∀ j, Module.Finite Aᵢ (Pᵢ.complex.X j)` hypothesis) is what
makes the degreewise Hom-tensor map an isomorphism; it holds for finite dimensional `Mᵢ` over the
finite dimensional `Aᵢ`. This `Extₖ` isomorphism is used in the derived-category `Etingof.Ext`
statement `Problem_8_2_8_ext` through the module-structure reconciliation and the
`Etingof.Ext ≃ Extₖ` comparison isomorphism. -/
noncomputable def Problem_8_2_8_extₖIso (i : ℕ)
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
    Extₖ k (A₁ ⊗[k] A₂)
        (extTensorFunctorLeftObj k A₁ A₂ (ModuleCat.of A₁ M₁) (ModuleCat.of A₂ M₂))
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) i
      ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
          Extₖ k A₁ (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1
            ⊗ Extₖ k A₂ (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2 :=
    -- Step 1: `Extⁱ` of the external tensor = `Hⁱ` of `Hom_{A₁⊗A₂}(P•₁ ⊗ₖ P•₂, N₁⊗ₖN₂)`.
    extIsoCohomologyHomₖ k (A₁ ⊗[k] A₂) _
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) (extTensorProjectiveResolutionLeft P₁ P₂) i ≪≫
    -- Step 2 & 3: rearrange to `Hom_{A₁}(P•₁,N₁) ⊗ₖ Hom_{A₂}(P•₂,N₂)`, then take `Hⁱ`.
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i).mapIso
        (rearrangeHomComplex k N₁ N₂ hN P₁ P₂) ≪≫
    -- Step 4a: cochain Künneth over the field for the tensor of the two Hom complexes.
    kunnethCochainComplexNatIso
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) i ≪≫
    -- Step 4b: identify the factor cohomologies as `Extⱼ^{A₁}` / `Extₘ^{A₂}`.
    Sigma.mapIso (fun p => tensorIso
      (extIsoCohomologyHomₖ k A₁ (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) P₁ p.1.1).symm
      (extIsoCohomologyHomₖ k A₂ (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) P₂ p.1.2).symm)

/-- **Problem 8.2.8, `Extₖ`**, `Nonempty` form: a one-line corollary of the isomorphism
`Problem_8_2_8_extₖIso`, kept for consumers phrased in terms of `Nonempty`. -/
theorem Problem_8_2_8_extₖ (i : ℕ)
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
      (Extₖ k (A₁ ⊗[k] A₂)
          (extTensorFunctorLeftObj k A₁ A₂ (ModuleCat.of A₁ M₁) (ModuleCat.of A₂ M₂))
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) i
        ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
            Extₖ k A₁ (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1
              ⊗ Extₖ k A₂ (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2) :=
  ⟨Problem_8_2_8_extₖIso k A₁ A₂ M₁ M₂ N₁ N₂ i P₁ P₂ hN⟩

-- The factor `k`-scalar towers on `Mᵢ` / `Nᵢ`: needed to form the finitely generated projective
-- `Etingof.barResolution` and consumed by `Problem_8_2_8_extₖ`. They only attach to
-- `Problem_8_2_8_ext` below (not to `Problem_8_2_8_extₖ`, which lists its `Nᵢ` towers explicitly).
variable [IsScalarTower k A₁ M₁] [IsScalarTower k A₂ M₂]
  [IsScalarTower k A₁ N₁] [IsScalarTower k A₂ N₂]

/-- **Problem 8.2.8, `Ext`.** For finite dimensional `k`-algebras `A₁, A₂`, finite dimensional
left modules `M₁, M₂` and finite dimensional left modules `N₁, N₂`, the `Ext` of the external
tensor products decomposes as a Künneth direct sum over the field `k`:
`Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) ≅ ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`.

`instM` / `instN` are the left external tensor product module structures on `M₁ ⊗ₖ M₂` and
`N₁ ⊗ₖ N₂`; `hM` / `hN` pin them to act componentwise on simple tensors. The summands are `k`-linear
tensor products of the factor `Ext` groups, which are `k`-modules via `Linear k (ModuleCat Aᵢ)`.

The iso is stated as a `k`-linear equivalence `≃ₗ[k]` (both sides are `k`-modules: the left via
`Linear k (ModuleCat (A₁ ⊗ₖ A₂))`, the right as a direct sum of `k`-tensor products). This matches
the strength of the `Tor` half `Problem_8_2_8_tor` (a `ModuleCat k` iso), and is strictly stronger
than a bare additive equivalence. The finite dimensionality of the `Mᵢ` is essential: it lets the
projective resolutions `Pᵢ` be chosen finitely generated projective, which is exactly the condition
under which the degreewise map
`Hom_{A₁}(P₁, N₁) ⊗ₖ Hom_{A₂}(P₂, N₂) → Hom_{A₁ ⊗ A₂}(P₁ ⊗ P₂, N₁ ⊗ N₂)` is an isomorphism. Without
it the natural Künneth map fails to be surjective (already at `i = 0`, `A₁ = A₂ = k`: the canonical
`M₁* ⊗ₖ M₂* → (M₁ ⊗ M₂)*` is not surjective for infinite dimensional `Mᵢ`). This degree-zero
counterexample is formalized as `TensorProduct.dualDistrib_not_surjective` in
`Problem8_2_8Counterexample.lean`; the departure from the book's stated scope (which asks only for
finite dimensional `Nᵢ`) is documented in `skipped-exercises.md`. -/
theorem Problem_8_2_8_ext (i : ℕ)
    [instM : Module (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)]
    [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    (hM : ∀ (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (m₁ ⊗ₜ[k] m₂ : M₁ ⊗[k] M₂)
        = (a₁ • m₁) ⊗ₜ[k] (a₂ • m₂))
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Nonempty
      (Etingof.Ext (ModuleCat.of (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂))
          (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)) i
        ≃ₗ[k] (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = i},
              TensorProduct k
                (Etingof.Ext (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1)
                (Etingof.Ext (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2))) := by
  -- The `k`-linear Künneth isomorphism `Problem_8_2_8_extₖ` is the mathematical core: it decomposes
  -- `Extₖ k (A₁⊗A₂) (extTensorFunctorLeftObj…) (N₁⊗N₂) i` as the categorical coproduct
  -- `∐_{j+m=i} Extₖ k A₁ M₁ N₁ j ⊗ Extₖ k A₂ M₂ N₂ m` in `ModuleCat k`. The proof combines it via:
  --   1. `Etingof.barResolution` (finitely generated projective, `instFiniteBarResolutionComplexX`
  --      + `instProjectiveBarModule`) resolves each `Mᵢ` and the external `M₁⊗M₂`; the tensor scalar
  --      towers come from `isScalarTower_extTensor`.
  --   2. `instModule_eq_extTensorModuleLeft` identifies the statement's `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)`
  --      (pinned by `hM`) with the canonical `extTensorFunctorLeftObj` (`hXM`); `instN`/`hN` are
  --      passed to `Problem_8_2_8_extₖ` directly on the `N` side.
  --   3. the comparison `extAbelianIsoExtₖ` (`Etingof.Ext ≃ₗ[k] Extₖ`) transports the big `Ext` and,
  --      backwards under `TensorProduct.congr`, each factor `Extₖ` summand.
  --   4. `ModuleCat.coprodIsoDirectSum` turns `∐` into `⨁`; the monoidal `⊗` in `ModuleCat k` is
  --      definitionally `TensorProduct k`, so `DirectSum.congrLinearEquiv` finishes.
  haveI : IsScalarTower k (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) := isScalarTower_extTensor instM hM
  haveI : IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) := isScalarTower_extTensor instN hN
  have hXM : (ModuleCat.of (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂) : ModuleCat.{u} (A₁ ⊗[k] A₂))
      = extTensorFunctorLeftObj k A₁ A₂ (ModuleCat.of A₁ M₁) (ModuleCat.of A₂ M₂) := by
    -- **Object identification.** The two objects both have carrier
    -- `M₁ ⊗[k] M₂` and act componentwise, but they are not *definitionally* equal:
    -- `extTensorFunctorLeftObj` bakes in `restrictModule₂L` (the `k`-structure on each factor
    -- obtained by restricting the `Aᵢ`-action along `k → Aᵢ`), whereas the statement's
    -- `ModuleCat.of (A₁⊗A₂)(M₁⊗M₂)` carries the ambient `Module k Mᵢ`. These agree by
    -- `IsScalarTower k Aᵢ Mᵢ`, but reconciling the two `k`-structures (carried through
    -- `extTensorModuleLeft` / `extTensorRepLeft`) is a self-contained module reconciliation.
    -- The factor identification is `restrictModule₁L`/`restrictModule₂L`
    -- (`= Module.compHom _ (algebraMap k Aᵢ)`) vs the ambient `Module k Mᵢ`, equal by
    -- `IsScalarTower.algebraMap_smul`. We reconcile by `subst`ing the ambient `Module k Mᵢ` with
    -- its restricted form `Module.compHom Mᵢ (algebraMap k Aᵢ)` (equal via `Module.ext'`), which
    -- makes the carriers `M₁ ⊗[k] M₂` definitionally equal. The residual `A₁⊗A₂`-action agreement
    -- is then `instModule_eq_extTensorModuleLeft`.
    have e1 : (inferInstance : Module k M₁) = Module.compHom M₁ (algebraMap k A₁) :=
      Module.ext' _ _ fun c m => (IsScalarTower.algebraMap_smul (A := A₁) c m).symm
    have e2 : (inferInstance : Module k M₂) = Module.compHom M₂ (algebraMap k A₂) :=
      Module.ext' _ _ fun c m => (IsScalarTower.algebraMap_smul (A := A₂) c m).symm
    subst e1 e2
    -- `subst` eliminated the ambient `Module k Mᵢ` instance binders; re-register the (now
    -- identical) restricted forms so typeclass resolution can supply
    -- `instModule_eq_extTensorModuleLeft`. `letI` (not `haveI`) keeps the binding transparent, so
    -- the synthesized instance is *definitionally* the `Module.compHom Mᵢ (algebraMap k Aᵢ)` that
    -- `subst` baked into `instM`'s carrier type.
    letI : Module k M₁ := Module.compHom M₁ (algebraMap k A₁)
    letI : Module k M₂ := Module.compHom M₂ (algebraMap k A₂)
    rw [instModule_eq_extTensorModuleLeft instM hM]
    -- Both sides are now `ModuleCat.of (A₁⊗A₂) (M₁ ⊗[k] M₂)` with the `extTensorModuleLeft`
    -- action over the restricted factor `k`-structures, to which `extTensorFunctorLeftObj` unfolds.
    rfl
  refine ⟨?_⟩
  refine (extAbelianIsoExtₖ k (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))
      (barResolution k (A₁ ⊗[k] A₂) (M₁ ⊗[k] M₂)) i) ≪≫ₗ ?_
  rw [hXM]
  refine (Problem_8_2_8_extₖIso k A₁ A₂ M₁ M₂ N₁ N₂ i
      (barResolution k A₁ M₁) (barResolution k A₂ M₂) hN).toLinearEquiv ≪≫ₗ ?_
  refine (ModuleCat.coprodIsoDirectSum _).toLinearEquiv ≪≫ₗ ?_
  exact DirectSum.congrLinearEquiv (fun p => TensorProduct.congr
    (extAbelianIsoExtₖ k (ModuleCat.of A₁ N₁) (barResolution k A₁ M₁) p.1.1).symm
    (extAbelianIsoExtₖ k (ModuleCat.of A₂ N₂) (barResolution k A₂ M₂) p.1.2).symm)

end Ext

end Etingof

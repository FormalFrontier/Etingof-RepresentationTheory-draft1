import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import EtingofRepresentationTheory.Chapter8.RearrangeComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorResolution
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Problem 8.2.8: Künneth formula for `Tor` and `Ext` over a tensor product of algebras

If `A₁, A₂` are algebras over a field `k`, and `Mᵢ, Nᵢ` are `Aᵢ`-modules, then

* `Torᵢ^{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Torⱼ^{A₁}(M₁, N₁) ⊗ₖ Torₘ^{A₂}(M₂, N₂)`,
* `Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`
  when the `Nᵢ` are finite dimensional.

All tensor products of the factor `Tor`/`Ext` on the right-hand side are over the **field `k`**, as
in the book: the objects are `k`-vector spaces and the Künneth summands are their `k`-linear tensor
products, not the (much larger) group-level `⊗_ℤ`.

## What is formalized here

The `Tor` statement is proved sorry-free below; the `Ext` statement is stated (spec-first, `sorry`
proof).

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
algebraic Künneth theorem over the field `kunnethChainComplexNat`, with the factor homologies
identified as `Torₖ` through `torIsoHomologyTensorRightₖ`. -/
theorem Problem_8_2_8_tor (i : ℕ)
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂)) :
    Nonempty
      (Torₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (extTensorFunctorObj k A₁ A₂ M₁ M₂) i
        ≅ ∐ fun p : {p : ℕ × ℕ // p.1 + p.2 = i} =>
            Torₖ k A₁ N₁ M₁ p.1.1 ⊗ Torₖ k A₂ N₂ M₂ p.1.2) := by
  -- Chosen projective resolutions of the two right modules, and of their external tensor.
  let P₁ : ProjectiveResolution M₁ := ProjectiveResolution.of M₁
  let P₂ : ProjectiveResolution M₂ := ProjectiveResolution.of M₂
  let Q : ProjectiveResolution (extTensorFunctorObj k A₁ A₂ M₁ M₂) :=
    extTensorProjectiveResolution P₁ P₂
  -- The two `k`-linear factor complexes `Cᵢ = P•ᵢ ⊗_{Aᵢ} Nᵢ`.
  refine ⟨
    -- Step 1: `Torᵢ` of the external tensor = `Hᵢ` of `(P•₁ ⊗_k P•₂) ⊗_{A₁⊗A₂} (N₁⊗ₖN₂)`.
    torIsoHomologyTensorRightₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)
        (extTensorFunctorObj k A₁ A₂ M₁ M₂) Q i ≪≫
    -- Step 2 & 3: rearrange the complex to `(P•₁ ⊗_{A₁} N₁) ⊗_k (P•₂ ⊗_{A₂} N₂)`, then take `Hᵢ`.
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
        (rearrangeComplex k A₁ A₂ N₁ N₂ hN P₁ P₂) ≪≫
    -- Step 4a: algebraic Künneth over the field for the tensor of the two factor complexes.
    (kunnethChainComplexNat
        (((tensorRightFunctorₖ k A₁ N₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex)
        (((tensorRightFunctorₖ k A₂ N₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₂.complex)
        i).some ≪≫
    -- Step 4b: identify the factor homologies as `Torⱼ^{A₁}` / `Torₘ^{A₂}`.
    Sigma.mapIso (fun p => tensorIso
      (torIsoHomologyTensorRightₖ k A₁ N₁ M₁ P₁ p.1.1).symm
      (torIsoHomologyTensorRightₖ k A₂ N₂ M₂ P₂ p.1.2).symm)⟩

end Tor

section Ext

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
-- left `Aᵢ`-modules `Mᵢ`, `Nᵢ`; the `Nᵢ` are finite dimensional over `k`
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [FiniteDimensional k N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [FiniteDimensional k N₂]

/-- **Problem 8.2.8, `Ext`.** For `k`-algebras `A₁, A₂`, left modules `M₁, M₂` and finite
dimensional left modules `N₁, N₂`, the `Ext` of the external tensor products decomposes as a
Künneth direct sum over the field `k`:
`Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) ≅ ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ₖ Extᵐ_{A₂}(M₂, N₂)`.

`instM` / `instN` are the left external tensor product module structures on `M₁ ⊗ₖ M₂` and
`N₁ ⊗ₖ N₂`; `hM` / `hN` pin them to act componentwise on simple tensors. The summands are `k`-linear
tensor products of the factor `Ext` groups, which are `k`-modules via `Linear k (ModuleCat Aᵢ)`. -/
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
        ≃+ (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = i},
              TensorProduct k
                (Etingof.Ext (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1)
                (Etingof.Ext (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2))) := by
  sorry

end Ext

end Etingof

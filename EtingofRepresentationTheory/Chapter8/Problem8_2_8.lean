import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Problem 8.2.8: Künneth formula for `Tor` and `Ext` over a tensor product of algebras

If `A₁, A₂` are algebras over a field `k`, and `Mᵢ, Nᵢ` are `Aᵢ`-modules, then

* `Torᵢ^{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Torⱼ^{A₁}(M₁, N₁) ⊗ Torₘ^{A₂}(M₂, N₂)`,
* `Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) = ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ Extᵐ_{A₂}(M₂, N₂)`
  when the `Nᵢ` are finite dimensional.

## What is formalized here

Both statements are stated below (spec-first, `sorry` proofs).

### The external tensor product module structures

The theorem's content lives in three tensor products of `k`-vector spaces: `A₁ ⊗ₖ A₂` (a
`k`-algebra, via `Algebra.TensorProduct`), `M₁ ⊗ₖ M₂`, and `N₁ ⊗ₖ N₂`. The key structures are:

* `N₁ ⊗ₖ N₂` is a **left** `A₁ ⊗ₖ A₂`-module with `(a₁ ⊗ a₂) • (n₁ ⊗ n₂) = (a₁ • n₁) ⊗ (a₂ • n₂)`;
* for `Tor`, `M₁ ⊗ₖ M₂` is a **right** `A₁ ⊗ₖ A₂`-module (i.e. a left `(A₁ ⊗ₖ A₂)ᵐᵒᵖ`-module) with
  `(m₁ ⊗ m₂) · (a₁ ⊗ a₂) = (m₁ · a₁) ⊗ (m₂ · a₂)`;
* for `Ext`, `M₁ ⊗ₖ M₂` is a **left** `A₁ ⊗ₖ A₂`-module, componentwise as for `N`.

Mathlib provides `TensorProduct.Algebra.module` (a `Module (A ⊗ B) M` from commuting `A`- and
`B`-actions on a *single* `M`), but the *external* tensor product module — where `A₁` acts on the
first factor and `A₂` on the second — is not a defeq-safe instance in the noncommutative setting
(the right-factor action is not a default instance, and one must transport along
`Algebra.TensorProduct.opAlgEquiv : (A₁ ⊗ A₂)ᵐᵒᵖ ≃ₐ A₁ᵐᵒᵖ ⊗ A₂ᵐᵒᵖ` on the `Tor` side). We
therefore take the module structures as parameters, **pinned** by their action on simple tensors
(`hN` / `hM` below). Because simple tensors generate the tensor product and the action is additive,
these hypotheses determine the structures uniquely: they are exactly the canonical external tensor
products. This is faithful and avoids the (statement-irrelevant) instance plumbing.

### The right-hand side

`Torⱼ^{A₁}(M₁, N₁)` is `Etingof.Tor A₁ N₁ M₁ j`, an `AddCommGrpCat`; the summands
`Torⱼ^{A₁}(M₁, N₁) ⊗ Torₘ^{A₂}(M₂, N₂)` are tensor products of abelian groups (over `ℤ`, the
group-level shadow of the book's `⊗ₖ`; the current `Tor`/`Ext` API forgets the `k`-linear
structure), and `⨁_{j+m=i}` is a `DirectSum` over `{p : ℕ × ℕ // p.1 + p.2 = i}`.
-/

open CategoryTheory TensorProduct DirectSum

namespace Etingof

universe u

section Tor

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
-- right `Aᵢ`-modules `Mᵢ` (`Module Aᵢᵐᵒᵖ`), also `k`-vector spaces so `M₁ ⊗ₖ M₂` makes sense
variable (M₁ M₂ : Type u)
  [AddCommGroup M₁] [Module k M₁] [Module A₁ᵐᵒᵖ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ᵐᵒᵖ M₂]
-- left `Aᵢ`-modules `Nᵢ`
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂]

/-- **Problem 8.2.8, `Tor`.** For `k`-algebras `A₁, A₂`, right modules `M₁, M₂` and left modules
`N₁, N₂`, the `Tor` of the external tensor products decomposes as a Künneth direct sum:
`Torᵢ^{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) ≅ ⨁_{j+m=i} Torⱼ^{A₁}(M₁, N₁) ⊗ Torₘ^{A₂}(M₂, N₂)`.

`instN` / `instM` are the external tensor product module structures on `N₁ ⊗ₖ N₂` (left) and
`M₁ ⊗ₖ M₂` (right); `hN` / `hM` pin them to act componentwise on simple tensors, which determines
them uniquely. -/
theorem Problem_8_2_8_tor (i : ℕ)
    [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
    [instM : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)]
    (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
      (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
        = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))
    (hM : ∀ (a₁ : A₁) (a₂ : A₂) (m₁ : M₁) (m₂ : M₂),
      (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (m₁ ⊗ₜ[k] m₂ : M₁ ⊗[k] M₂)
        = (MulOpposite.op a₁ • m₁) ⊗ₜ[k] (MulOpposite.op a₂ • m₂)) :
    Nonempty
      (Etingof.Tor (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)
          (ModuleCat.of (A₁ ⊗[k] A₂)ᵐᵒᵖ (M₁ ⊗[k] M₂)) i
        ≅ AddCommGrpCat.of
            (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = i},
              TensorProduct ℤ
                (Etingof.Tor A₁ N₁ (ModuleCat.of A₁ᵐᵒᵖ M₁) p.1.1)
                (Etingof.Tor A₂ N₂ (ModuleCat.of A₂ᵐᵒᵖ M₂) p.1.2))) := by
  sorry

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
Künneth direct sum:
`Extⁱ_{A₁ ⊗ A₂}(M₁ ⊗ M₂, N₁ ⊗ N₂) ≅ ⨁_{j+m=i} Extʲ_{A₁}(M₁, N₁) ⊗ Extᵐ_{A₂}(M₂, N₂)`.

`instM` / `instN` are the left external tensor product module structures on `M₁ ⊗ₖ M₂` and
`N₁ ⊗ₖ N₂`; `hM` / `hN` pin them to act componentwise on simple tensors. -/
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
              TensorProduct ℤ
                (Etingof.Ext (ModuleCat.of A₁ M₁) (ModuleCat.of A₁ N₁) p.1.1)
                (Etingof.Ext (ModuleCat.of A₂ M₂) (ModuleCat.of A₂ N₂) p.1.2))) := by
  sorry

end Ext

end Etingof

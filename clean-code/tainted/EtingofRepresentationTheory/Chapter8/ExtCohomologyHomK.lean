import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The `k`-linear `Ext` functor and `Ext = Hⁿ(Hom(P•, N))`

For `k`-algebras `A` the Künneth / rearrangement work on `Ext` over a tensor product of algebras
(Problem 8.2.8, `Ext` half) needs the cohomological analogue of the `Tor` package in
`Chapter8/TensorRightFunctorK.lean`. On the `Tor` side, `Etingof.Torₖ` refines `Tor` to a
`ModuleCat k`-valued functor and `Etingof.torIsoHomologyTensorRightₖ` identifies `Torₙᴬ(M, N)` with
the `n`-th homology of the `k`-linear complex `P• ⊗_A N` (via
`ProjectiveResolution.isoLeftDerivedObj`).

This file provides the dual, cohomological package for `Ext`, built on Mathlib's `k`-linear
`Ext`-functor `Ext k (ModuleCat A) n : (ModuleCat A)ᵒᵖ ⥤ ModuleCat A ⥤ ModuleCat k`
(the `n`-th left derived functor of the linear Yoneda bifunctor, so `ModuleCat k`-valued, matching
`Torₖ`):

* `Etingof.Extₖ k A M N n : ModuleCat k`: `Extⁿ_A(M, N)` as a `k`-vector space.
* `Etingof.extIsoCohomologyHomₖ`: for any projective resolution `P•` of `M`, the `k`-linear iso
  `Extⁿ_A(M, N) ≅ Hⁿ(Hom_A(P•, N))`, where `Hom_A(P•, N) = P.complex.linearYonedaObj k N` is the
  cochain complex `n ↦ Hom_A(Pₙ, N)`. This is `ProjectiveResolution.isoExt`, the cohomological
  analogue of `torIsoHomologyTensorRightₖ`.

The `k`-linear structure comes from `ModuleCat.linearOverField` (`Linear k (ModuleCat A)` for a
`k`-algebra `A` over a field `k`); `Ext` (root namespace) additionally needs
`EnoughProjectives (ModuleCat A)` (present for any ring `A`).

Note this is the `ModuleCat k`-valued left-derived-functor `Ext`, not the `AddCommGroup`-valued
derived-category `Etingof.Ext = CategoryTheory.Abelian.Ext` used in the statement of
`Problem_8_2_8_ext`. The two agree as abelian groups; identifying them is done by the `Ext`
comparison (Problem 8.2.8, `Ext` half), which uses the cohomological identification below exactly
as `Problem_8_2_8_tor` uses `torIsoHomologyTensorRightₖ`.
-/

open CategoryTheory Limits

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]

/-- `Extⁿ_A(M, N)` as a `k`-vector space: the `n`-th `k`-linear `Ext`-functor
(`Ext k (ModuleCat A) n`, the left derived functor of the linear Yoneda bifunctor)
evaluated at the left `A`-modules `M`, `N`. This is the `k`-linear refinement of `Ext` used by the
Künneth formula of Problem 8.2.8, which tensors the factor `Ext`s over the field `k`. The
cohomological analogue of `Etingof.Torₖ`. -/
noncomputable def Extₖ (M N : ModuleCat.{u} A) (n : ℕ) : ModuleCat.{u} k :=
  ((_root_.Ext k (ModuleCat.{u} A) n).obj (Opposite.op M)).obj N

/-- **`Extₖ` from a chosen projective resolution.** For any projective resolution `P•` of the left
`A`-module `M`, `Extⁿ_A(M, N)` (as a `k`-vector space) is canonically isomorphic to the `n`-th
homology of the `k`-linear cochain complex `Hom_A(P•, N)` (`P.complex.linearYonedaObj k N`, whose
degree-`n` term is `Hom_A(Pₙ, N)`). The `k`-linear, cohomological analogue of
`Etingof.torIsoHomologyTensorRightₖ`, obtained from `ProjectiveResolution.isoExt`. -/
noncomputable def extIsoCohomologyHomₖ (M N : ModuleCat.{u} A) (P : ProjectiveResolution M)
    (n : ℕ) :
    Extₖ k A M N n ≅ (P.complex.linearYonedaObj k N).homology n :=
  P.isoExt n N

end Etingof

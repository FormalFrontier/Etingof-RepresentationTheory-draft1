import Mathlib

/-!
# Problem 3.8.4: scalar extension and the Noether-Deuring theorem

> **(i)** Let `V, W` be finite dimensional representations of an algebra `A` over a (not
> necessarily algebraically closed) field `K`. Let `L` be a field extension of `K`. Suppose
> that `V ⊗_K L` is isomorphic to `W ⊗_K L` as a module over the `L`-algebra `A ⊗_K L`. Show
> that `V` and `W` are isomorphic as `A`-modules.
>
> **(ii)** (The Noether-Deuring theorem) In the setting of (i), suppose that `V ⊗_K L` is a
> direct summand in `W ⊗_K L`. Show that `V` is a direct summand in `W`.

The book's hint reduces to a finite extension of degree `n`, identifies `V ⊗_K L` and
`W ⊗_K L` with `Vⁿ` and `Wⁿ` as `A`-modules, and applies the Krull-Schmidt theorem, valid
over an arbitrary field by Problem 3.8.3, recorded here as
`Etingof.Problem3_8_3.krull_schmidt_uniqueness`.

## Base change

Mathlib registers the base-changed scalar `L ⊗[K] V` (scalar factor on the left) rather
than `V ⊗_K L`; the two are canonically isomorphic and we use `L ⊗[K] V` throughout, so the
book's `A ⊗_K L`-module `V ⊗_K L` is modelled by the `L ⊗[K] A`-module `L ⊗[K] V`.

The `L ⊗[K] A`-action on `L ⊗[K] V` is not a Mathlib instance (the general
`TensorProduct.Algebra.module` is deliberately not global, to avoid a scalar-action diamond
on `A ⊗[R] A`). We build it here directly: base change the representation `A →ₐ[K] End K V`
along `L`, then use the universal property `AlgHom.liftEquiv` of `L ⊗[K] A` to obtain an
`L`-algebra map `L ⊗[K] A →ₐ[L] End L (L ⊗[K] V)`, and turn it into a module structure with
`Module.compHom`.
-/

open scoped TensorProduct

namespace Etingof.Problem3_8_4

variable {K A V W L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [Field L] [Algebra K L]

/-- The representation of `A` on the base change `L ⊗[K] V`, acting `L`-linearly on the right
factor. It is the composite of the representation `A →ₐ[K] End K V` with the base-change
algebra map `End K V →ₐ[K] End L (L ⊗[K] V)`. -/
noncomputable def rep : A →ₐ[K] Module.End L (L ⊗[K] V) :=
  (Module.End.baseChangeHom K L V).comp (Algebra.lsmul K K V)

/-- The `L ⊗[K] A`-representation on `L ⊗[K] V`, from the universal property of base change. -/
noncomputable def repTensor : (L ⊗[K] A) →ₐ[L] Module.End L (L ⊗[K] V) :=
  AlgHom.liftEquiv K L A (Module.End L (L ⊗[K] V)) (rep (A := A) (V := V) (L := L))

/-- The base change `L ⊗[K] V` as a module over the base-changed algebra `L ⊗[K] A`. This is
the Lean model of the book's `A ⊗_K L`-module `V ⊗_K L`. -/
noncomputable instance bcMod : Module (L ⊗[K] A) (L ⊗[K] V) :=
  Module.compHom (L ⊗[K] V) (R := Module.End L (L ⊗[K] V))
    (repTensor (A := A) (V := V) (L := L)).toRingHom

/-!
The two general-`L` theorems of Problem 3.8.4 are proved downstream, above the finite-extension
case (`Problem3_8_4_Finite.lean`) and the descent step (`Problem3_8_4_Descent.lean`) in the import
DAG. They cannot live here: those two files import this base module, so proving the theorems here
would create an import cycle.

* Part (i), `iso_of_baseChange_iso`: if `L ⊗[K] V ≅ L ⊗[K] W` as `L ⊗[K] A`-modules then `V ≅ W`
  as `A`-modules; proved in `Problem3_8_4_Main.lean`.
* Part (ii), the Noether-Deuring theorem `directSummand_of_baseChange_directSummand`: if `L ⊗[K] V`
  is a direct summand of `L ⊗[K] W` (a split injection `(i, p)` with `p ∘ i = id`) then `V` is a
  direct summand of `W`; proved in `Problem3_8_4_General.lean`.
-/

end Etingof.Problem3_8_4

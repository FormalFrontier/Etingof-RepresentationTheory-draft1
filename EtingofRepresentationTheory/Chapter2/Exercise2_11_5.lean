import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Exercise 2.11.5: Base change of algebras and modules

Let `K` be a field and `L` an extension of `K`.

* If `A` is a `K`-algebra, then `A ⊗_K L` is naturally an `L`-algebra.
* If `V` is an `A`-module, then `V ⊗_K L` has a natural structure of a module over `A ⊗_K L`.

The `L`-algebra structure is Mathlib's `Algebra.TensorProduct.rightAlgebra` (base change of the
scalar factor on the right), for which the structure map is `l ↦ 1 ⊗ₜ l`. The module part is
recorded as the existence of the natural `(A ⊗_K L)`-module structure on `V ⊗_K L` whose action on
pure tensors is `(a ⊗ l) • (v ⊗ l') = (a • v) ⊗ (l · l')`.

The `L`-algebra part is fully constructed and its structure map identified; the module part is a
statement (existence) to be proved in a later phase.
-/

namespace Etingof.Exercise2_11_5

open scoped TensorProduct

variable (K L A V : Type*) [CommRing K] [CommRing L] [Algebra K L] [Ring A] [Algebra K A]

/-- The natural `L`-algebra structure on the base change `A ⊗_K L`. (Etingof Exercise 2.11.5) -/
noncomputable instance instRightAlgebra : Algebra L (A ⊗[K] L) :=
  Algebra.TensorProduct.rightAlgebra

/-- The structure map of the `L`-algebra `A ⊗_K L` sends `l` to `1 ⊗ l`. -/
theorem algebraMap_right_apply (l : L) :
    (algebraMap L (A ⊗[K] L)) l = 1 ⊗ₜ[K] l :=
  rfl

/-- If `V` is an `A`-module, then `V ⊗_K L` carries a natural `(A ⊗_K L)`-module structure whose
action on pure tensors is `(a ⊗ l) • (v ⊗ l') = (a • v) ⊗ (l · l')`. (Etingof Exercise 2.11.5) -/
theorem exists_module_baseChange [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower K A V] :
    ∃ inst : Module (A ⊗[K] L) (V ⊗[K] L),
      ∀ (a : A) (l l' : L) (v : V),
        (letI := inst; (a ⊗ₜ[K] l) • (v ⊗ₜ[K] l')) = (a • v) ⊗ₜ[K] (l * l') :=
  sorry

end Etingof.Exercise2_11_5

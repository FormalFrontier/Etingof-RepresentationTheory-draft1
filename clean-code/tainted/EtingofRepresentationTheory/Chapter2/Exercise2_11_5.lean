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

The `L`-algebra part is fully constructed and its structure map identified (`instRightAlgebra` /
`algebraMap_right_apply`); the module part is proved in-file by `exists_module_baseChange`, which
transports the base-change action across `TensorProduct.comm` and assembles the
`Module (A ⊗_K L) (V ⊗_K L)` instance via `TensorProduct.Algebra.module`, verifying the pure-tensor
action `(a ⊗ l) • (v ⊗ l') = (a • v) ⊗ (l · l')`.
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
        (letI := inst; (a ⊗ₜ[K] l) • (v ⊗ₜ[K] l')) = (a • v) ⊗ₜ[K] (l * l') := by
  -- `V ⊗_K L` is an `A`-module via the left factor (this is a global instance). We equip it with an
  -- `L`-module structure acting on the right factor by transporting the standard base-change action
  -- of `L` on `L ⊗_K V` across the commutativity isomorphism `e : V ⊗_K L ≃ₗ[K] L ⊗_K V`. The two
  -- actions commute over `K`, so `TensorProduct.Algebra.module` assembles them into the desired
  -- `(A ⊗_K L)`-module structure with `(a ⊗ l) • m = a • l • m`.
  let e : V ⊗[K] L ≃ₗ[K] L ⊗[K] V := TensorProduct.comm K V L
  letI sm : SMul L (V ⊗[K] L) := ⟨fun l x => e.symm (l • e x)⟩
  have hsmul : ∀ (l : L) (x : V ⊗[K] L), e (l • x) = l • e x :=
    fun l x => e.apply_symm_apply _
  letI mod : Module L (V ⊗[K] L) :=
    Function.Injective.module L e.toLinearMap.toAddMonoidHom e.injective hsmul
  -- The `L`-action on pure tensors: `l • (v ⊗ l') = v ⊗ (l * l')`.
  have smul_tmul_L : ∀ (l l' : L) (v : V), l • (v ⊗ₜ[K] l') = v ⊗ₜ[K] (l * l') := by
    intro l l' v
    apply e.injective
    rw [hsmul]
    simp only [e, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  letI tower : IsScalarTower K L (V ⊗[K] L) := by
    refine ⟨fun k l x => e.injective ?_⟩
    simp only [hsmul, map_smul]
    exact smul_assoc k l (e x)
  letI comm : SMulCommClass A L (V ⊗[K] L) := by
    refine ⟨fun a l x => ?_⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v l' =>
      rw [smul_tmul_L, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_tmul_L]
    | add x y hx hy => simp only [smul_add, hx, hy]
  refine ⟨TensorProduct.Algebra.module, fun a l l' v => ?_⟩
  rw [TensorProduct.Algebra.smul_def, smul_tmul_L, TensorProduct.smul_tmul']

end Etingof.Exercise2_11_5

-- The leaf name follows Mathlib conventions; the underscore comes solely from the stable
-- book-number namespace Exercise2_11_5, which is part of this project's public API.
attribute [nolint defsWithUnderscore] Etingof.Exercise2_11_5.instRightAlgebra

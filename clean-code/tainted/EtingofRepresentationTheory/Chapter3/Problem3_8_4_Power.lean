import EtingofRepresentationTheory.Chapter3.Problem3_8_4

/-!
# Problem 3.8.4, base change as a power: `L ⊗_K V ≅ Vⁿ` as an `A`-module

Prerequisite for Problem 3.8.4. The base change `L ⊗[K] V` carries an
`L ⊗[K] A`-module structure `Etingof.Problem3_8_4.bcMod`, under which `a : A` acts on
`l ⊗ v` through `1 ⊗ a` as `l ⊗ (a • v)`; that is, `A` acts on the right (`V`) tensor
factor only. Restricting scalars along the inclusion
`Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A`, `a ↦ 1 ⊗ a`, therefore views
`L ⊗[K] V` as an `A`-module (`bcModRestrict`).

When `L / K` is finite of degree `n = finrank K L`, this restricted `A`-module is a finite
power of `V`: choosing a `K`-basis `b : Module.Basis (Fin n) K L` gives an `A`-linear
isomorphism `L ⊗[K] V ≃ₗ[A] (Fin n → V)`, `l ⊗ v ↦ (i ↦ b.repr l i • v)`. This is the
identification the book uses to reduce Problem 3.8.4 to the Krull-Schmidt theorem applied to
`Vⁿ ≅ Wⁿ`.

The underlying `K`-linear equivalence and the reduction of `repTensor` on pure tensors are
proved before the `bcModRestrict` instance is introduced: once that extra `Module A`
instance is in scope it perturbs the typeclass search that elaborates `rep`/`repTensor` and
`TensorProduct.comm`, so those results are established first.
-/

open scoped TensorProduct

namespace Etingof.Problem3_8_4

variable {K A V L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [Field L] [Algebra K L]

/-- The representation `repTensor` sends `1 ⊗ a` to the operator `l ⊗ v ↦ l ⊗ (a • v)`.
Proved before the restricted `A`-module instance is in scope. -/
theorem repTensor_one_tmul_apply (a : A) (l : L) (v : V) :
    repTensor (A := A) (V := V) (L := L) (1 ⊗ₜ[K] a) (l ⊗ₜ[K] v) = l ⊗ₜ[K] (a • v) := by
  rw [repTensor, AlgHom.liftEquiv_tmul, one_smul]
  simp [rep, Module.End.baseChangeHom, LinearMap.baseChange_tmul, Algebra.lsmul_apply]

section Pow

variable {n : ℕ}

/-- The underlying `K`-linear isomorphism `L ⊗[K] V ≃ₗ[K] (Fin n → V)` attached to a
`K`-basis `b` of `L`: transpose the tensor factors, expand `L` in the basis, and identify
`V ⊗[K] (Fin n → K)` with `Fin n → V`. On pure tensors `l ⊗ v ↦ (i ↦ b.repr l i • v)`. -/
noncomputable def toPiLinearEquiv (b : Module.Basis (Fin n) K L) :
    (L ⊗[K] V) ≃ₗ[K] (Fin n → V) :=
  (TensorProduct.comm K L V) ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl K V) b.equivFun) ≪≫ₗ
    (TensorProduct.piScalarRight K K V (Fin n))

@[simp]
theorem toPiLinearEquiv_tmul (b : Module.Basis (Fin n) K L) (l : L) (v : V) :
    toPiLinearEquiv b (l ⊗ₜ[K] v) = fun i => b.repr l i • v := by
  simp only [toPiLinearEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, Module.Basis.equivFun_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]

end Pow

/-- The `A`-module structure on the base change `L ⊗[K] V`, obtained by restricting the
`L ⊗[K] A`-module `bcMod` along the inclusion
`Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A`, `a ↦ 1 ⊗ a`. Under it `a : A` acts
as `l ⊗ v ↦ l ⊗ (a • v)`; see `bcModRestrict_smul_tmul`. -/
noncomputable instance bcModRestrict : Module A (L ⊗[K] V) :=
  Module.compHom (L ⊗[K] V)
    (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom

/-- Unfolding of the restricted scalar action: `a • x = (1 ⊗ a) • x`, the latter using the
`L ⊗[K] A`-module `bcMod`. -/
theorem bcModRestrict_smul (a : A) (x : L ⊗[K] V) :
    (a • x : L ⊗[K] V) =
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A) a) • x :=
  rfl

/-- The `L ⊗[K] A`-action of `bcMod` is application of the representation `repTensor`. -/
theorem bcMod_smul (y : L ⊗[K] A) (x : L ⊗[K] V) :
    (y • x : L ⊗[K] V) = repTensor (A := A) (V := V) (L := L) y x :=
  rfl

/-- `A` acts on the base change through the right factor: `a • (l ⊗ v) = l ⊗ (a • v)`. -/
theorem bcModRestrict_smul_tmul (a : A) (l : L) (v : V) :
    (a • (l ⊗ₜ[K] v) : L ⊗[K] V) = l ⊗ₜ[K] (a • v) := by
  rw [bcModRestrict_smul, bcMod_smul, Algebra.TensorProduct.includeRight_apply,
    repTensor_one_tmul_apply]

section Pow

variable {n : ℕ}

/-- The `K`-linear identification `toPiLinearEquiv b`, packaged as an `A`-linear map for the
restricted `A`-action on `L ⊗[K] V`. Since `A` acts only on the `V` factor and the `K`-scalars
`b.repr l i` commute with the `A`-action (`SMulCommClass K A V`, automatic from
`IsScalarTower K A V`), the map intertwines the two `A`-module structures. -/
noncomputable def toPiAlinMap (b : Module.Basis (Fin n) K L) :
    (L ⊗[K] V) →ₗ[A] (Fin n → V) where
  toFun := toPiLinearEquiv b
  map_add' := (toPiLinearEquiv b).map_add
  map_smul' a x := by
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l v =>
      rw [bcModRestrict_smul_tmul, toPiLinearEquiv_tmul, toPiLinearEquiv_tmul]
      funext i
      simp only [Pi.smul_apply]
      exact smul_comm (b.repr l i) a v
    | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The `A`-linear isomorphism `L ⊗[K] V ≃ₗ[A] (Fin n → V)` from a `K`-basis of `L`: the
`K`-linear equivalence `toPiLinearEquiv b`, which is also `A`-linear (`toPiAlinMap`). -/
noncomputable def toPiAlinEquiv (b : Module.Basis (Fin n) K L) :
    (L ⊗[K] V) ≃ₗ[A] (Fin n → V) :=
  LinearEquiv.ofBijective (toPiAlinMap b) (toPiLinearEquiv b).bijective

end Pow

/-- **Problem 3.8.4 prerequisite.** For a finite extension `L / K` of degree
`n = finrank K L`, the base change `L ⊗[K] V`, viewed as an `A`-module by restricting the
`L ⊗[K] A`-action along `includeRight`, is `A`-linearly isomorphic to the power `Vⁿ`.

Choosing a `K`-basis of `L` gives the isomorphism `l ⊗ v ↦ (i ↦ b.repr l i • v)`; see
`toPiAlinEquiv`. -/
theorem baseChange_alinEquiv_pow [FiniteDimensional K L] :
    Nonempty ((L ⊗[K] V) ≃ₗ[A] (Fin (Module.finrank K L) → V)) :=
  ⟨toPiAlinEquiv (Module.finBasis K L)⟩

end Etingof.Problem3_8_4

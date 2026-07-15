import EtingofRepresentationTheory.Chapter8.Definition8_2_3

/-!
# The `k`-linear structure on `tensorOver A N M`

`Etingof.tensorOver A N M` (Definition 8.2.3) is the ring-tensor `M ⊗_A N`, realised as the
quotient of the additive tensor product `M ⊗_ℤ N` by the balancing subgroup. When `A` is an
algebra over a commutative ring `k` and both `M` and `N` carry compatible `k`-actions (so that
`k` acts centrally, commuting with the `A`-action), the tensor product `M ⊗_A N` is naturally a
`k`-module. This file constructs that structure.

This is the missing prerequisite for the Künneth / four-fold rearrangement work on `Tor` for a
tensor product of algebras (Problem 8.2.8): the target of the rearrangement isomorphism,
`(P₁ ⊗_{A₁} N₁) ⊗_k (P₂ ⊗_{A₂} N₂)`, tensors two ring-tensor-overs over `k`, which only typechecks
once each factor is a `k`-module.

## Construction

`M ⊗_ℤ N` is already a `k`-module via `TensorProduct.leftModule` (the left `k`-action on `M`
transported to the tensor product), with `c • (m ⊗ₜ n) = (c • m) ⊗ₜ n`. The balancing subgroup

  `⟨(m · a) ⊗ n - m ⊗ (a • n)⟩`

is invariant under this action: `c • ((m · a) ⊗ n - m ⊗ (a • n)) = ((c • m) · a) ⊗ n
- (c • m) ⊗ (a • n)`, using that the `k`-action commutes with the right `A`-action on `M`
(`SMulCommClass k Aᵐᵒᵖ M`). Hence the action descends to the quotient `tensorOver A N M`.
-/

open TensorProduct

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]
variable (M : Type u) [AddCommGroup M] [Module Aᵐᵒᵖ M]
  [Module k M] [SMulCommClass k Aᵐᵒᵖ M]

/-- The balancing subgroup is invariant under the left `k`-action on `M ⊗_ℤ N`: scaling the
generator `(m · a) ⊗ n - m ⊗ (a • n)` by `c` gives the generator for `c • m`. -/
theorem balancedSubgroup_smul_mem (c : k) {x : TensorProduct ℤ M N}
    (hx : x ∈ balancedSubgroup A N M) : c • x ∈ balancedSubgroup A N M := by
  -- it suffices that `c • ·` maps the generating set into the balancing subgroup
  have h : balancedSubgroup A N M ≤ (balancedSubgroup A N M).comap
      (DistribSMul.toAddMonoidHom (TensorProduct ℤ M N) c) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨a, m, n, rfl⟩
    change c • ((MulOpposite.op a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)) ∈ balancedSubgroup A N M
    rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_comm c (MulOpposite.op a) m]
    exact AddSubgroup.subset_closure ⟨a, c • m, n, rfl⟩
  exact AddSubgroup.mem_comap.mp (h hx)

noncomputable instance : SMul k (tensorOver A N M) where
  smul c := QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom _ c)
    (fun _ hx => AddSubgroup.mem_comap.mpr (balancedSubgroup_smul_mem k A N M c hx))

variable {k A N M}

/-- The `k`-action on `tensorOver A N M` sends the class of `x` to the class of `c • x`. -/
@[simp]
theorem smul_mk (c : k) (x : TensorProduct ℤ M N) :
    c • (QuotientAddGroup.mk x : tensorOver A N M) = QuotientAddGroup.mk (c • x) := rfl

variable (k A N M)

noncomputable instance : Module k (tensorOver A N M) where
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [smul_mk, one_smul]
  mul_smul c d x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [smul_mk, smul_mk, smul_mk, mul_smul]
  smul_zero c := by
    rw [← QuotientAddGroup.mk_zero, smul_mk, smul_zero]
  smul_add c x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b => rw [← QuotientAddGroup.mk_add, smul_mk, smul_mk, smul_mk,
          ← QuotientAddGroup.mk_add, smul_add]
  add_smul c d x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [smul_mk, smul_mk, smul_mk, ← QuotientAddGroup.mk_add, add_smul]
  zero_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a => rw [smul_mk, zero_smul, QuotientAddGroup.mk_zero]

end Etingof

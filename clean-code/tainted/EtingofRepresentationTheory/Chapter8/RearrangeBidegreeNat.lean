import EtingofRepresentationTheory.Chapter8.RearrangeBidegree

set_option backward.isDefEq.respectTransparency false

/-!
# Naturality of the single-bidegree rearrangement isomorphism

Milestone (b) of the four-fold rearrangement (Problem 8.2.8, `Tor`). Building on milestone (a)
(`Etingof.rearrangeBidegree`, `RearrangeBidegree.lean`), we show the bidegree iso is **natural** in
the two right-module arguments `P₁`, `P₂`.

For right-module maps `f₁ : P₁ →ₗ[A₁ᵐᵒᵖ] P₁'` and `f₂ : P₂ →ₗ[A₂ᵐᵒᵖ] P₂'`, the square

```
  (P₁ ⊗ₖ P₂) ⊗_{A₁⊗A₂} (N₁ ⊗ₖ N₂)  ──rearrangeBidegree──▸  (P₁ ⊗_{A₁} N₁) ⊗ₖ (P₂ ⊗_{A₂} N₂)
             │                                                          │
   induced by f₁ ⊗ₖ f₂                                    tensorRightMap f₁ ⊗ₖ tensorRightMap f₂
             ▼                                                          ▼
  (P₁' ⊗ₖ P₂') ⊗_{A₁⊗A₂} (N₁ ⊗ₖ N₂) ─rearrangeBidegree─▸ (P₁' ⊗_{A₁} N₁) ⊗ₖ (P₂' ⊗_{A₂} N₂)
```

commutes (`rearrangeBidegree_naturality`). This is exactly what makes the iso commute with the
Koszul-signed total-complex differential `d = d₁ ⊗ 1 + (-1)ʲ 1 ⊗ d₂` in milestone (c).

The vertical maps are the `k`-linear functoriality of `tensorOver` in its right-module argument,
packaged here as `Etingof.tensorOverMapₖ`. Since both sides agree on simple-tensor generators, the
proof reduces (via `QuotientAddGroup.mk_surjective` + `TensorProduct.induction_on`) to the two
factorwise generator computations.
-/

open TensorProduct

namespace Etingof

universe u

/-! ### `k`-linear functoriality of `tensorOver` in the right-module argument -/

section GenericMap

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A]
variable (P : Type u) [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
variable (P' : Type u) [AddCommGroup P'] [Module k P'] [Module Aᵐᵒᵖ P'] [SMulCommClass k Aᵐᵒᵖ P']
variable (N : Type u) [AddCommGroup N] [Module A N]
variable (f : P →ₗ[k] P')

/-- The underlying `ℤ`-linear map `P ⊗ℤ N → P' ⊗_A N`, `p ⊗ n ↦ ⟦f p ⊗ n⟧`, used to build the
`k`-linear induced map `tensorOverMapₖ`. -/
noncomputable def tensorOverMapφ : TensorProduct ℤ P N →ₗ[ℤ] tensorOver A N P' :=
  (QuotientAddGroup.mk' (balancedSubgroup A N P')).toIntLinearMap.comp
    (TensorProduct.map f.toAddMonoidHom.toIntLinearMap LinearMap.id)

omit [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P'] in
@[simp] theorem tensorOverMapφ_tmul (p : P) (n : N) :
    tensorOverMapφ k A P P' N f (p ⊗ₜ[ℤ] n)
      = (QuotientAddGroup.mk (f p ⊗ₜ[ℤ] n) : tensorOver A N P') := by
  simp [tensorOverMapφ]

omit [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P] in
/-- `tensorOverMapφ` is `k`-linear: the action lands on the `P` factor and `f` is `k`-linear. -/
theorem tensorOverMapφ_smul (c : k) (w : TensorProduct ℤ P N) :
    tensorOverMapφ k A P P' N f (c • w) = c • tensorOverMapφ k A P P' N f w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul p n =>
      rw [TensorProduct.smul_tmul', tensorOverMapφ_tmul, tensorOverMapφ_tmul, map_smul, smul_mk,
        TensorProduct.smul_tmul']

variable (hf : ∀ (a : Aᵐᵒᵖ) (p : P), f (a • p) = a • f p)
include hf

omit [SMulCommClass k Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P'] in
/-- `tensorOverMapφ` sends the balancing subgroup of `P` into `0` (via `f`'s `Aᵐᵒᵖ`-linearity),
hence descends to `tensorOver A N P`. -/
theorem tensorOverMapφ_ker (w : TensorProduct ℤ P N) (hw : w ∈ balancedSubgroup A N P) :
    tensorOverMapφ k A P P' N f w = 0 := by
  have hle : balancedSubgroup A N P ≤ (tensorOverMapφ k A P P' N f).toAddMonoidHom.ker := by
    rw [balancedSubgroup, AddSubgroup.closure_le]
    rintro x ⟨a, p, n, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      tensorOverMapφ_tmul, hf, sub_eq_zero]
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact AddSubgroup.subset_closure ⟨a, f p, n, rfl⟩
  exact hle hw

/-- The `k`-linear induced map `tensorOver A N P → tensorOver A N P'`, `⟦p ⊗ n⟧ ↦ ⟦f p ⊗ n⟧`,
associated to a `k`-linear, `Aᵐᵒᵖ`-compatible map `f : P → P'`. -/
noncomputable def tensorOverMapₖ : tensorOver A N P →ₗ[k] tensorOver A N P' :=
  liftTensorOver k A N P (tensorOver A N P') (tensorOverMapφ k A P P' N f)
    (tensorOverMapφ_smul k A P P' N f) (tensorOverMapφ_ker k A P P' N f hf)

@[simp] theorem tensorOverMapₖ_mk (p : P) (n : N) :
    tensorOverMapₖ k A P P' N f hf (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n))
      = (QuotientAddGroup.mk (f p ⊗ₜ[ℤ] n) : tensorOver A N P') := by
  rw [tensorOverMapₖ, liftTensorOver_mk, tensorOverMapφ_tmul]

end GenericMap

/-! ### Restricting an `Aᵐᵒᵖ`-linear map to `k` along the scalar tower -/

section RestrictK

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]
variable (P P' : Type u)
  [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ P]
  [AddCommGroup P'] [Module k P'] [Module Aᵐᵒᵖ P'] [IsScalarTower k Aᵐᵒᵖ P']

/-- An `Aᵐᵒᵖ`-linear map between modules over which `k` acts through `Aᵐᵒᵖ` (scalar tower) is
`k`-linear. -/
noncomputable def restrictK (f : P →ₗ[Aᵐᵒᵖ] P') : P →ₗ[k] P' where
  toFun := f
  map_add' := f.map_add
  map_smul' c p := by
    simp only [RingHom.id_apply]
    have h1 : (c • (1 : Aᵐᵒᵖ)) • p = c • p := by rw [smul_assoc, one_smul]
    have h2 : (c • (1 : Aᵐᵒᵖ)) • (f p) = c • f p := by rw [smul_assoc, one_smul]
    rw [← h1, map_smul, h2]

@[simp] theorem restrictK_apply (f : P →ₗ[Aᵐᵒᵖ] P') (p : P) : restrictK k A P P' f p = f p := rfl

theorem restrictK_op_smul (f : P →ₗ[Aᵐᵒᵖ] P') (a : Aᵐᵒᵖ) (p : P) :
    restrictK k A P P' f (a • p) = a • restrictK k A P P' f p := f.map_smul a p

end RestrictK

/-! ### Naturality of `rearrangeBidegree` -/

section Naturality

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (P₁ P₂ P₁' P₂' : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ᵐᵒᵖ P₁]
    [IsScalarTower k A₁ᵐᵒᵖ P₁] [SMulCommClass k A₁ᵐᵒᵖ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ᵐᵒᵖ P₂]
    [IsScalarTower k A₂ᵐᵒᵖ P₂] [SMulCommClass k A₂ᵐᵒᵖ P₂]
  [AddCommGroup P₁'] [Module k P₁'] [Module A₁ᵐᵒᵖ P₁']
    [IsScalarTower k A₁ᵐᵒᵖ P₁'] [SMulCommClass k A₁ᵐᵒᵖ P₁']
  [AddCommGroup P₂'] [Module k P₂'] [Module A₂ᵐᵒᵖ P₂']
    [IsScalarTower k A₂ᵐᵒᵖ P₂'] [SMulCommClass k A₂ᵐᵒᵖ P₂']
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instM : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
    [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
variable [instM' : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁' ⊗[k] P₂')]
    [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁' ⊗[k] P₂')]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hM : ∀ (a₁ : A₁) (a₂ : A₂) (p₁ : P₁) (p₂ : P₂),
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (p₁ ⊗ₜ[k] p₂ : P₁ ⊗[k] P₂)
      = (MulOpposite.op a₁ • p₁) ⊗ₜ[k] (MulOpposite.op a₂ • p₂))
  (hM' : ∀ (a₁ : A₁) (a₂ : A₂) (p₁ : P₁') (p₂ : P₂'),
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (p₁ ⊗ₜ[k] p₂ : P₁' ⊗[k] P₂')
      = (MulOpposite.op a₁ • p₁) ⊗ₜ[k] (MulOpposite.op a₂ • p₂))
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))
variable (f₁ : P₁ →ₗ[A₁ᵐᵒᵖ] P₁') (f₂ : P₂ →ₗ[A₂ᵐᵒᵖ] P₂')

omit [SMulCommClass k A₁ᵐᵒᵖ P₁] [SMulCommClass k A₂ᵐᵒᵖ P₂] [SMulCommClass k A₁ᵐᵒᵖ P₁']
  [SMulCommClass k A₂ᵐᵒᵖ P₂'] [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
  [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁' ⊗[k] P₂')] in
include hM hM' in
/-- The `k`-linear map `f₁ ⊗ₖ f₂ : P₁ ⊗ₖ P₂ → P₁' ⊗ₖ P₂'` is compatible with the external
`(A₁ ⊗ A₂)ᵐᵒᵖ`-actions pinned by `hM` / `hM'`. This is the hypothesis needed to induce a map on
the external `tensorOver`. -/
theorem map_ext_op_smul (r : (A₁ ⊗[k] A₂)ᵐᵒᵖ) (x : P₁ ⊗[k] P₂) :
    TensorProduct.map (restrictK k A₁ P₁ P₁' f₁) (restrictK k A₂ P₂ P₂' f₂) (r • x)
      = r • TensorProduct.map (restrictK k A₁ P₁ P₁' f₁) (restrictK k A₂ P₂ P₂' f₂) x := by
  obtain ⟨g, rfl⟩ : ∃ g, MulOpposite.op g = r := ⟨r.unop, rfl⟩
  induction g using TensorProduct.induction_on generalizing x with
  | zero => simp
  | add g g' ih ih' =>
      rw [MulOpposite.op_add, add_smul, map_add, ih, ih', add_smul]
  | tmul a₁ a₂ =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
      | tmul p₁ p₂ =>
          rw [hM]
          simp only [TensorProduct.map_tmul, restrictK_op_smul]
          rw [hM']

include hM hM' hN in
/-- **Milestone (b).** Naturality of the single-bidegree rearrangement isomorphism in the two
right-module arguments. The rearrangement iso intertwines the `tensorOver`-functoriality of
`f₁ ⊗ₖ f₂` (on the external tensor) with `tensorRightMap f₁ ⊗ₖ tensorRightMap f₂` (factorwise). -/
theorem rearrangeBidegree_naturality :
    (TensorProduct.map
          (tensorOverMapₖ k A₁ P₁ P₁' N₁ (restrictK k A₁ P₁ P₁' f₁)
            (restrictK_op_smul k A₁ P₁ P₁' f₁))
          (tensorOverMapₖ k A₂ P₂ P₂' N₂ (restrictK k A₂ P₂ P₂' f₂)
            (restrictK_op_smul k A₂ P₂ P₂' f₂))).comp
        (rearrangeBidegree k A₁ A₂ P₁ P₂ N₁ N₂ hM hN).toLinearMap
      = (rearrangeBidegree k A₁ A₂ P₁' P₂' N₁ N₂ hM' hN).toLinearMap.comp
          (tensorOverMapₖ k (A₁ ⊗[k] A₂) (P₁ ⊗[k] P₂) (P₁' ⊗[k] P₂') (N₁ ⊗[k] N₂)
            (TensorProduct.map (restrictK k A₁ P₁ P₁' f₁) (restrictK k A₂ P₂ P₂' f₂))
            (map_ext_op_smul k A₁ A₂ P₁ P₂ P₁' P₂' hM hM' f₁ f₂)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp only [QuotientAddGroup.mk_add, map_add, hw, hw']
  | tmul x y =>
      induction x using TensorProduct.induction_on generalizing y with
      | zero => simp
      | add x x' hx hx' =>
          simp only [add_tmul, QuotientAddGroup.mk_add, map_add, hx, hx']
      | tmul p₁ p₂ =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y y' hy hy' =>
              simp only [tmul_add, QuotientAddGroup.mk_add, map_add, hy, hy']
          | tmul n₁ n₂ =>
              simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, rearrangeBidegree_mk_tmul,
                TensorProduct.map_tmul, tensorOverMapₖ_mk, restrictK_apply]

end Naturality

end Etingof

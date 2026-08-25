import EtingofRepresentationTheory.Chapter8.TensorOverModule
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.TensorProduct.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Single-bidegree rearrangement isomorphism for the `Tor` Künneth formula

Milestone (a) of the four-fold rearrangement (Problem 8.2.8, `Tor`). For `k`-algebras `A₁, A₂`,
right modules `P₁, P₂` (the degreewise pieces of projective resolutions) and left modules
`N₁, N₂`, we construct a `k`-linear isomorphism

  `(P₁ ⊗ₖ P₂) ⊗_{A₁ ⊗ A₂} (N₁ ⊗ₖ N₂)  ≃ₗ[k]  (P₁ ⊗_{A₁} N₁) ⊗ₖ (P₂ ⊗_{A₂} N₂)`

sending `⟦(p₁ ⊗ₖ p₂) ⊗ (n₁ ⊗ₖ n₂)⟧ ↦ ⟦p₁ ⊗ n₁⟧ ⊗ₖ ⟦p₂ ⊗ n₂⟧`, where `⊗_A` is the ring tensor
product `Etingof.tensorOver` of Definition 8.2.3 (a quotient of the `ℤ`-tensor by the balancing
subgroup) and `⊗ₖ` is the tensor product over the field `k`.

The external `A₁ ⊗ A₂`-module structures on `P₁ ⊗ₖ P₂` (right) and `N₁ ⊗ₖ N₂` (left) are taken as
parameters pinned on simple tensors by `hM` / `hN`, mirroring
`Etingof.Problem_8_2_8_tor`. The `k`-module structure on each factor `Pᵢ ⊗_{Aᵢ} Nᵢ` is the one
from `Etingof.TensorOverModule` (`k` acting on the left factor `Pᵢ`).

## The `k`-through-`A` hypotheses

Well-definedness of the map with respect to the *inner* `k`-balancing of `N₁ ⊗ₖ N₂` requires the
identity `⟦p ⊗ (c • n)⟧ = c • ⟦p ⊗ n⟧` in `Pᵢ ⊗_{Aᵢ} Nᵢ`. Since the ambient `k`-action on
`tensorOver` acts through the *left* factor, this identity holds exactly when `k` acts on `Pᵢ` and
`Nᵢ` through `Aᵢ`, i.e. via the scalar towers `IsScalarTower k Aᵢᵐᵒᵖ Pᵢ` and
`IsScalarTower k Aᵢ Nᵢ`. This is precisely the "`k → Z(Aᵢ)`" compatibility required by the construction: in the
application the `k`-structure on each module is the restriction of scalars of its `Aᵢ`-structure.
-/

open TensorProduct

namespace Etingof

universe u

/-! ### Per-factor `k`-linear quotient map `P ⊗ₖ N → P ⊗_A N` -/

section Factor

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]
variable (P : Type u) [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P]
    [IsScalarTower k Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The balancing relation, read on the quotient: `⟦(p · a) ⊗ n⟧ = ⟦p ⊗ (a • n)⟧`. -/
theorem tensorOver_mk_op_smul (a : A) (p : P) (n : N) :
    (QuotientAddGroup.mk ((MulOpposite.op a • p) ⊗ₜ[ℤ] n) : tensorOver A N P)
      = QuotientAddGroup.mk (p ⊗ₜ[ℤ] (a • n)) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure ⟨a, p, n, rfl⟩

/-- Moving a central scalar `c : k` from the right factor `N` to the ambient `k`-action:
`⟦p ⊗ (c • n)⟧ = c • ⟦p ⊗ n⟧`. Uses that `k` acts through `A` on both `P` and `N`. -/
theorem tensorOver_mk_smul_right (c : k) (p : P) (n : N) :
    (QuotientAddGroup.mk (p ⊗ₜ[ℤ] (c • n)) : tensorOver A N P)
      = c • (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n)) := by
  rw [Etingof.smul_mk, TensorProduct.smul_tmul', QuotientAddGroup.eq]
  have hn : (c • n) = (algebraMap k A c) • n := by
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  have hp : (c • p) = (MulOpposite.op (algebraMap k A c)) • p := by
    have : (MulOpposite.op (algebraMap k A c)) = c • (1 : Aᵐᵒᵖ) := by
      rw [Algebra.algebraMap_eq_smul_one]; rfl
    rw [this, smul_assoc, one_smul]
  rw [hn, hp]
  exact AddSubgroup.subset_closure ⟨algebraMap k A c, p, n, by abel⟩

/-- The `k`-bilinear map `(p, n) ↦ ⟦p ⊗ n⟧` used to build `tensorOverMk`. -/
noncomputable def tensorOverBil : P →ₗ[k] N →ₗ[k] tensorOver A N P :=
  LinearMap.mk₂ k (fun p n => (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n) : tensorOver A N P))
    (fun p₁ p₂ n => by rw [add_tmul]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p n => by rw [← TensorProduct.smul_tmul', Etingof.smul_mk])
    (fun p n₁ n₂ => by rw [tmul_add]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p n => tensorOver_mk_smul_right k A P N c p n)

/-- The canonical `k`-linear map `P ⊗ₖ N → P ⊗_A N`, `p ⊗ₖ n ↦ ⟦p ⊗ n⟧`. Well-defined because,
under the `k`-through-`A` hypotheses, the ambient `k`-action on `P ⊗_A N` factors the inner
`k`-balancing of `P ⊗ₖ N`. -/
noncomputable def tensorOverMk : (P ⊗[k] N) →ₗ[k] tensorOver A N P :=
  TensorProduct.lift (tensorOverBil k A P N)

@[simp] theorem tensorOverMk_tmul (p : P) (n : N) :
    tensorOverMk k A P N (p ⊗ₜ[k] n) = (QuotientAddGroup.mk (p ⊗ₜ[ℤ] n) : tensorOver A N P) :=
  TensorProduct.lift.tmul _ _

end Factor

/-! ### Descending a `k`-linear map through the balancing quotient -/

section Lift

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A]
variable (N : Type u) [AddCommGroup N] [Module A N]
variable (P : Type u) [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
variable (M : Type u) [AddCommGroup M] [Module k M]

/-- Descend a `k`-linear map out of the additive tensor `P ⊗ℤ N` that is invariant under the
`k`-action and kills the balancing subgroup, to a `k`-linear map out of `P ⊗_A N`. -/
noncomputable def liftTensorOver (φ : TensorProduct ℤ P N →ₗ[ℤ] M)
    (hsmul : ∀ (c : k) (w : TensorProduct ℤ P N), φ (c • w) = c • φ w)
    (hker : ∀ w ∈ balancedSubgroup A N P, φ w = 0) :
    tensorOver A N P →ₗ[k] M where
  toFun := QuotientAddGroup.lift _ φ.toAddMonoidHom hker
  map_add' x y := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add]
    simp only [QuotientAddGroup.lift_mk, map_add]
  map_smul' c z := by
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [Etingof.smul_mk]
    simp only [QuotientAddGroup.lift_mk, LinearMap.toAddMonoidHom_coe, RingHom.id_apply]
    exact hsmul c w

@[simp] theorem liftTensorOver_mk (φ : TensorProduct ℤ P N →ₗ[ℤ] M)
    (hsmul : ∀ (c : k) (w : TensorProduct ℤ P N), φ (c • w) = c • φ w)
    (hker : ∀ w ∈ balancedSubgroup A N P, φ w = 0) (w : TensorProduct ℤ P N) :
    liftTensorOver k A N P M φ hsmul hker (QuotientAddGroup.mk w) = φ w :=
  rfl

end Lift

/-! ### The rearrangement, on the `k`-tensor level -/

section Main

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (P₁ P₂ : Type u)
  [AddCommGroup P₁] [Module k P₁] [Module A₁ᵐᵒᵖ P₁]
    [IsScalarTower k A₁ᵐᵒᵖ P₁] [SMulCommClass k A₁ᵐᵒᵖ P₁]
  [AddCommGroup P₂] [Module k P₂] [Module A₂ᵐᵒᵖ P₂]
    [IsScalarTower k A₂ᵐᵒᵖ P₂] [SMulCommClass k A₂ᵐᵒᵖ P₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]

/-- The underlying `k`-linear rearrangement of the four-fold `k`-tensor:
`(p₁ ⊗ p₂) ⊗ (n₁ ⊗ n₂) ↦ ⟦p₁ ⊗ n₁⟧ ⊗ₖ ⟦p₂ ⊗ n₂⟧`. -/
noncomputable def rearrangeAux :
    (P₁ ⊗[k] P₂) ⊗[k] (N₁ ⊗[k] N₂) →ₗ[k]
      (tensorOver A₁ N₁ P₁) ⊗[k] (tensorOver A₂ N₂ P₂) :=
  (TensorProduct.map (tensorOverMk k A₁ P₁ N₁) (tensorOverMk k A₂ P₂ N₂)).comp
    (TensorProduct.tensorTensorTensorComm k P₁ P₂ N₁ N₂).toLinearMap

@[simp] theorem rearrangeAux_tmul (p₁ : P₁) (p₂ : P₂) (n₁ : N₁) (n₂ : N₂) :
    rearrangeAux k A₁ A₂ P₁ P₂ N₁ N₂ ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[k] (n₁ ⊗ₜ[k] n₂))
      = (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ P₂) := by
  simp [rearrangeAux]

variable [instM : Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
    [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]

variable
  (hM : ∀ (a₁ : A₁) (a₂ : A₂) (p₁ : P₁) (p₂ : P₂),
    (MulOpposite.op (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂)) • (p₁ ⊗ₜ[k] p₂ : P₁ ⊗[k] P₂)
      = (MulOpposite.op a₁ • p₁) ⊗ₜ[k] (MulOpposite.op a₂ • p₂))
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

omit [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] in
include hM hN in
/-- The key compatibility: `rearrangeAux` sends the external `A₁ ⊗ A₂`-balancing relation on the
left to `0`, i.e. `rearrangeAux ((op g • m) ⊗ n) = rearrangeAux (m ⊗ (g • n))`. Proved by
reduction to simple tensors, where it is the two factorwise balancing relations. -/
theorem rearrangeAux_balanced (g : A₁ ⊗[k] A₂) (m : P₁ ⊗[k] P₂) (n : N₁ ⊗[k] N₂) :
    rearrangeAux k A₁ A₂ P₁ P₂ N₁ N₂ ((MulOpposite.op g • m) ⊗ₜ[k] n)
      = rearrangeAux k A₁ A₂ P₁ P₂ N₁ N₂ (m ⊗ₜ[k] (g • n)) := by
  induction g using TensorProduct.induction_on generalizing m n with
  | zero => simp
  | add g₁ g₂ ih₁ ih₂ =>
      simp only [MulOpposite.op_add, add_smul, add_tmul, map_add, ih₁, ih₂, tmul_add]
  | tmul a₁ a₂ =>
      induction m using TensorProduct.induction_on generalizing n with
      | zero => simp
      | add m₁ m₂ ihm₁ ihm₂ =>
          simp only [smul_add, add_tmul, map_add, ihm₁, ihm₂]
      | tmul p₁ p₂ =>
          induction n using TensorProduct.induction_on with
          | zero => simp
          | add n₁ n₂ ihn₁ ihn₂ =>
              simp only [tmul_add, smul_add, map_add, ihn₁, ihn₂]
          | tmul n₁ n₂ =>
              rw [hM, hN, rearrangeAux_tmul, rearrangeAux_tmul,
                tensorOver_mk_op_smul, tensorOver_mk_op_smul]

/-! ### The forward map `⟦(p₁ ⊗ p₂) ⊗ (n₁ ⊗ n₂)⟧ ↦ ⟦p₁ ⊗ n₁⟧ ⊗ₖ ⟦p₂ ⊗ n₂⟧` -/

/-- The forward map before descending the balancing quotient: the additive lift of `rearrangeAux`
along the comparison `TensorProduct ℤ _ _ → _ ⊗ₖ _`. -/
noncomputable def fwdPre :
    TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂) →ₗ[ℤ]
      (tensorOver A₁ N₁ P₁) ⊗[k] (tensorOver A₂ N₂ P₂) :=
  TensorProduct.lift <| LinearMap.mk₂ ℤ
    (fun x y => rearrangeAux k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[k] y))
    (fun x₁ x₂ y => by rw [add_tmul, map_add])
    (fun c x y => by rw [← TensorProduct.smul_tmul', map_zsmul])
    (fun x y₁ y₂ => by rw [tmul_add, map_add])
    (fun c x y => by rw [TensorProduct.tmul_smul, map_zsmul])

omit instM [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] instN in
@[simp] theorem fwdPre_tmul (x : P₁ ⊗[k] P₂) (y : N₁ ⊗[k] N₂) :
    fwdPre k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[ℤ] y)
      = rearrangeAux k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[k] y) :=
  TensorProduct.lift.tmul _ _

omit instM [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] instN in
theorem fwdPre_smul (c : k) (w : TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂)) :
    fwdPre k A₁ A₂ P₁ P₂ N₁ N₂ (c • w) = c • fwdPre k A₁ A₂ P₁ P₂ N₁ N₂ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul x y =>
      rw [TensorProduct.smul_tmul', fwdPre_tmul, fwdPre_tmul, ← TensorProduct.smul_tmul', map_smul]

omit [SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (P₁ ⊗[k] P₂)] in
include hM hN in
/-- `fwdPre` kills the external `A₁ ⊗ A₂`-balancing subgroup, hence descends to `tensorOver`. -/
theorem fwdPre_mem_ker (w : TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂))
    (hw : w ∈ balancedSubgroup (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :
    fwdPre k A₁ A₂ P₁ P₂ N₁ N₂ w = 0 := by
  have hle : balancedSubgroup (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)
      ≤ (fwdPre k A₁ A₂ P₁ P₂ N₁ N₂).toAddMonoidHom.ker := by
    rw [balancedSubgroup, AddSubgroup.closure_le]
    rintro x ⟨g, m, n, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      fwdPre_tmul, sub_eq_zero]
    exact rearrangeAux_balanced k A₁ A₂ P₁ P₂ N₁ N₂ hM hN g m n
  exact hle hw

include hM hN in
/-- **Milestone (a), forward direction.** The `k`-linear map
`(P₁ ⊗ₖ P₂) ⊗_{A₁ ⊗ A₂} (N₁ ⊗ₖ N₂) → (P₁ ⊗_{A₁} N₁) ⊗ₖ (P₂ ⊗_{A₂} N₂)`. -/
noncomputable def fwd :
    tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) →ₗ[k]
      (tensorOver A₁ N₁ P₁) ⊗[k] (tensorOver A₂ N₂ P₂) where
  toFun := QuotientAddGroup.lift _ (fwdPre k A₁ A₂ P₁ P₂ N₁ N₂).toAddMonoidHom
    (fwdPre_mem_ker k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
  map_add' x y := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add]
    simp only [QuotientAddGroup.lift_mk, map_add]
  map_smul' c z := by
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [Etingof.smul_mk]
    simp only [QuotientAddGroup.lift_mk, LinearMap.toAddMonoidHom_coe, RingHom.id_apply]
    exact fwdPre_smul k A₁ A₂ P₁ P₂ N₁ N₂ c w

@[simp] theorem fwd_mk_tmul (p₁ : P₁) (p₂ : P₂) (n₁ : N₁) (n₂ : N₂) :
    fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN
        (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ P₂) := by
  simp only [fwd, LinearMap.coe_mk, AddHom.coe_mk, QuotientAddGroup.lift_mk,
    LinearMap.toAddMonoidHom_coe, fwdPre_tmul, rearrangeAux_tmul]

/-! ### The inverse map `⟦p₁ ⊗ n₁⟧ ⊗ₖ ⟦p₂ ⊗ n₂⟧ ↦ ⟦(p₁ ⊗ p₂) ⊗ (n₁ ⊗ n₂)⟧` -/

/-- For fixed `p₁, n₁`, the `ℤ`-linear map `P₂ ⊗ℤ N₂ → L`,
`p₂ ⊗ n₂ ↦ ⟦(p₁ ⊗ p₂) ⊗ (n₁ ⊗ n₂)⟧`. -/
noncomputable def invInner (p₁ : P₁) (n₁ : N₁) :
    TensorProduct ℤ P₂ N₂ →ₗ[ℤ] tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  TensorProduct.lift <| LinearMap.mk₂ ℤ
    (fun p₂ n₂ => (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
        tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)))
    (fun p₂ p₂' n₂ => by rw [tmul_add, add_tmul]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p₂ n₂ => by
      rw [tmul_smul, ← TensorProduct.smul_tmul']
      exact map_zsmul (QuotientAddGroup.mk' _) _ _)
    (fun p₂ n₂ n₂' => by rw [tmul_add, tmul_add]; exact map_add (QuotientAddGroup.mk' _) _ _)
    (fun c p₂ n₂ => by
      rw [tmul_smul, TensorProduct.tmul_smul]
      exact map_zsmul (QuotientAddGroup.mk' _) _ _)

set_option linter.unusedSectionVars false in
@[simp] theorem invInner_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ (p₂ ⊗ₜ[ℤ] n₂)
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  TensorProduct.lift.tmul _ _

/-- `invInner` is `k`-linear (the `k`-action lands on the left factor `P₁`). -/
theorem invInner_smul (p₁ : P₁) (n₁ : N₁) (c : k)
    (w : TensorProduct ℤ P₂ N₂) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ (c • w)
      = c • invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul p₂ n₂ =>
      rw [TensorProduct.smul_tmul', invInner_tmul, invInner_tmul, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', ← Etingof.smul_mk]

/-- `invInner` is additive in `p₁`. -/
theorem invInner_add_left (p₁ p₁' : P₁) (n₁ : N₁) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ (p₁ + p₁') n₁
      = invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ + invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁' n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [invInner_tmul, LinearMap.add_apply]
  rw [add_tmul, add_tmul]
  exact map_add (QuotientAddGroup.mk' _) _ _

/-- `invInner` is `ℤ`-linear in `p₁`. -/
theorem invInner_zsmul_left (c : ℤ) (p₁ : P₁) (n₁ : N₁) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ (c • p₁) n₁ = c • invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [invInner_tmul, LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
  exact map_zsmul (QuotientAddGroup.mk' _) _ _

/-- `invInner` is additive in `n₁`. -/
theorem invInner_add_right (p₁ : P₁) (n₁ n₁' : N₁) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ (n₁ + n₁')
      = invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ + invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁' := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [invInner_tmul, LinearMap.add_apply]
  rw [add_tmul, tmul_add]
  exact map_add (QuotientAddGroup.mk' _) _ _

/-- `invInner` is `ℤ`-linear in `n₁`. -/
theorem invInner_zsmul_right (c : ℤ) (p₁ : P₁) (n₁ : N₁) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ (c • n₁) = c • invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [invInner_tmul, LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  exact map_zsmul (QuotientAddGroup.mk' _) _ _

/-- `invInner` is `k`-linear in `p₁`. -/
theorem invInner_ksmul_left (c : k) (p₁ : P₁) (n₁ : N₁) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ (c • p₁) n₁ = c • invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ := by
  refine TensorProduct.ext' fun p₂ n₂ => ?_
  simp only [invInner_tmul, LinearMap.smul_apply]
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', ← Etingof.smul_mk]

include hM hN in
/-- `invInner p₁ n₁` kills the factor-2 balancing subgroup (via `hM`/`hN` at `a₁ = 1`). -/
theorem invInner_mem_ker (p₁ : P₁) (n₁ : N₁) (w : TensorProduct ℤ P₂ N₂)
    (hw : w ∈ balancedSubgroup A₂ N₂ P₂) :
    invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ w = 0 := by
  have hle : balancedSubgroup A₂ N₂ P₂
      ≤ (invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁).toAddMonoidHom.ker := by
    rw [balancedSubgroup, AddSubgroup.closure_le]
    rintro x ⟨a₂, p₂, n₂, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      invInner_tmul, sub_eq_zero, QuotientAddGroup.eq_iff_sub_mem]
    apply AddSubgroup.subset_closure
    refine ⟨(1 : A₁) ⊗ₜ[k] a₂, p₁ ⊗ₜ[k] p₂, n₁ ⊗ₜ[k] n₂, ?_⟩
    rw [hM, hN]
    simp [MulOpposite.op_one]
  exact hle hw

include hM hN in
/-- For fixed `p₁, n₁`, the descended `k`-linear map `P₂ ⊗_{A₂} N₂ → L`. -/
noncomputable def invMidInner (p₁ : P₁) (n₁ : N₁) :
    tensorOver A₂ N₂ P₂ →ₗ[k] tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  liftTensorOver k A₂ N₂ P₂ _ (invInner k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁)
    (invInner_smul k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁)
    (invInner_mem_ker k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁)

include hM hN in
@[simp] theorem invMidInner_mk (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    invMidInner k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁
        (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) := by
  rw [invMidInner, liftTensorOver_mk, invInner_tmul]

include hM hN in
/-- `invMidInner` is `k`-linear in `p₁`. -/
theorem invMidInner_ksmul_left (c : k) (p₁ : P₁) (n₁ : N₁) :
    invMidInner k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (c • p₁) n₁
      = c • invMidInner k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁ := by
  ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
  simp only [invMidInner, liftTensorOver_mk, LinearMap.smul_apply]
  exact LinearMap.congr_fun (invInner_ksmul_left k A₁ A₂ P₁ P₂ N₁ N₂ c p₁ n₁) w

include hM hN in
/-- The `ℤ`-bilinear map `P₁ × N₁ → (P₂ ⊗_{A₂} N₂ →ₗ[k] L)` assembling `invMidInner`. -/
noncomputable def invMid :
    P₁ →ₗ[ℤ] N₁ →ₗ[ℤ]
      (tensorOver A₂ N₂ P₂ →ₗ[k] tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  LinearMap.mk₂ ℤ (fun p₁ n₁ => invMidInner k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁)
    (fun p₁ p₁' n₁ => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [invMidInner, liftTensorOver_mk, LinearMap.add_apply,
        LinearMap.congr_fun (invInner_add_left k A₁ A₂ P₁ P₂ N₁ N₂ p₁ p₁' n₁) w])
    (fun c p₁ n₁ => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [invMidInner, liftTensorOver_mk, LinearMap.smul_apply,
        LinearMap.congr_fun (invInner_zsmul_left k A₁ A₂ P₁ P₂ N₁ N₂ c p₁ n₁) w])
    (fun p₁ n₁ n₁' => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [invMidInner, liftTensorOver_mk, LinearMap.add_apply,
        LinearMap.congr_fun (invInner_add_right k A₁ A₂ P₁ P₂ N₁ N₂ p₁ n₁ n₁') w])
    (fun c p₁ n₁ => by
      ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
      simp only [invMidInner, liftTensorOver_mk, LinearMap.smul_apply,
        LinearMap.congr_fun (invInner_zsmul_right k A₁ A₂ P₁ P₂ N₁ N₂ c p₁ n₁) w])

include hM hN in
/-- The forward map before descending the factor-1 balancing quotient. -/
noncomputable def invBilPre :
    TensorProduct ℤ P₁ N₁ →ₗ[ℤ]
      (tensorOver A₂ N₂ P₂ →ₗ[k] tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  TensorProduct.lift (invMid k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)

include hM hN in
@[simp] theorem invBilPre_tmul (p₁ : P₁) (n₁ : N₁) :
    invBilPre k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (p₁ ⊗ₜ[ℤ] n₁)
      = invMidInner k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁ :=
  TensorProduct.lift.tmul _ _

include hM hN in
/-- `invBilPre` is `k`-linear (the `k`-action lands on the left factor `P₁`). -/
theorem invBilPre_smul (c : k) (w : TensorProduct ℤ P₁ N₁) :
    invBilPre k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (c • w)
      = c • invBilPre k A₁ A₂ P₁ P₂ N₁ N₂ hM hN w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul p₁ n₁ =>
      rw [TensorProduct.smul_tmul', invBilPre_tmul, invBilPre_tmul,
        invMidInner_ksmul_left k A₁ A₂ P₁ P₂ N₁ N₂ hM hN c p₁ n₁]

include hM hN in
/-- `invBilPre` kills the factor-1 balancing subgroup (via `hM`/`hN` at `a₂ = 1`). -/
theorem invBilPre_mem_ker (w : TensorProduct ℤ P₁ N₁) (hw : w ∈ balancedSubgroup A₁ N₁ P₁) :
    invBilPre k A₁ A₂ P₁ P₂ N₁ N₂ hM hN w = 0 := by
  have hle : balancedSubgroup A₁ N₁ P₁
      ≤ (invBilPre k A₁ A₂ P₁ P₂ N₁ N₂ hM hN).toAddMonoidHom.ker := by
    rw [balancedSubgroup, AddSubgroup.closure_le]
    rintro x ⟨a₁, p₁, n₁, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe, map_sub,
      invBilPre_tmul, sub_eq_zero]
    ext t₂; obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t₂
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [QuotientAddGroup.mk_add, map_add, ha, hb]
    | tmul p₂ n₂ =>
        simp only [invMidInner_mk, QuotientAddGroup.eq_iff_sub_mem]
        apply AddSubgroup.subset_closure
        refine ⟨a₁ ⊗ₜ[k] (1 : A₂), p₁ ⊗ₜ[k] p₂, n₁ ⊗ₜ[k] n₂, ?_⟩
        rw [hM, hN]
        simp [MulOpposite.op_one]
  exact hle hw

include hM hN in
/-- The bilinear map `(P₁ ⊗_{A₁} N₁) × (P₂ ⊗_{A₂} N₂) → L` for the inverse. -/
noncomputable def invBil :
    tensorOver A₁ N₁ P₁ →ₗ[k] tensorOver A₂ N₂ P₂ →ₗ[k]
      tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  liftTensorOver k A₁ N₁ P₁ _ (invBilPre k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
    (invBilPre_smul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
    (invBilPre_mem_ker k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)

include hM hN in
@[simp] theorem invBil_mk_mk (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    invBil k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁))
        (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) := by
  rw [invBil, liftTensorOver_mk, invBilPre_tmul, invMidInner_mk]

include hM hN in
/-- **Milestone (a), inverse direction.** The `k`-linear map
`(P₁ ⊗_{A₁} N₁) ⊗ₖ (P₂ ⊗_{A₂} N₂) → (P₁ ⊗ₖ P₂) ⊗_{A₁ ⊗ A₂} (N₁ ⊗ₖ N₂)`. -/
noncomputable def inv :
    (tensorOver A₁ N₁ P₁) ⊗[k] (tensorOver A₂ N₂ P₂) →ₗ[k]
      tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) :=
  TensorProduct.lift (invBil k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)

include hM hN in
@[simp] theorem inv_mk_tmul_mk (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    inv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN
        ((QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ P₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) := by
  rw [inv, TensorProduct.lift.tmul, invBil_mk_mk]

/-! ### The two round-trips and the equivalence -/

include hM hN in
theorem fwd_mk (w : TensorProduct ℤ (P₁ ⊗[k] P₂) (N₁ ⊗[k] N₂)) :
    fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (QuotientAddGroup.mk w)
      = fwdPre k A₁ A₂ P₁ P₂ N₁ N₂ w := rfl

include hM hN in
/-- `inv` undoes `rearrangeAux` on a `ℤ`-simple tensor `x ⊗ y` of `k`-tensors. -/
theorem inv_rearrangeAux (x : P₁ ⊗[k] P₂) (y : N₁ ⊗[k] N₂) :
    inv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (rearrangeAux k A₁ A₂ P₁ P₂ N₁ N₂ (x ⊗ₜ[k] y))
      = QuotientAddGroup.mk (x ⊗ₜ[ℤ] y) := by
  induction x using TensorProduct.induction_on generalizing y with
  | zero => simp
  | add x x' hx hx' =>
      simp only [add_tmul, map_add, hx, hx', QuotientAddGroup.mk_add]
  | tmul p₁ p₂ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
          simp only [tmul_add, map_add, hy, hy', QuotientAddGroup.mk_add]
      | tmul n₁ n₂ => rw [rearrangeAux_tmul, inv_mk_tmul_mk]

include hM hN in
theorem inv_fwd (z : tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :
    inv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN z) = z := by
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [fwd_mk]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, QuotientAddGroup.mk_add]
  | tmul x y => rw [fwdPre_tmul, inv_rearrangeAux]

include hM hN in
theorem fwd_invBil (t₁ : tensorOver A₁ N₁ P₁) (t₂ : tensorOver A₂ N₂ P₂) :
    fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (invBil k A₁ A₂ P₁ P₂ N₁ N₂ hM hN t₁ t₂) = t₁ ⊗ₜ[k] t₂ := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective t₁
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t₂
  induction u using TensorProduct.induction_on generalizing v with
  | zero => simp
  | add u u' hu hu' =>
      simp only [QuotientAddGroup.mk_add, map_add, LinearMap.add_apply, add_tmul, hu, hu']
  | tmul p₁ n₁ =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' =>
          simp only [QuotientAddGroup.mk_add, map_add, tmul_add, hv, hv']
      | tmul p₂ n₂ => rw [invBil_mk_mk, fwd_mk_tmul]

include hM hN in
theorem fwd_inv (r : (tensorOver A₁ N₁ P₁) ⊗[k] (tensorOver A₂ N₂ P₂)) :
    fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN (inv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r r' hr hr' => simp only [map_add, hr, hr']
  | tmul t₁ t₂ =>
      rw [inv, TensorProduct.lift.tmul]
      exact fwd_invBil k A₁ A₂ P₁ P₂ N₁ N₂ hM hN t₁ t₂

include hM hN in
/-- **Milestone (a).** The single-bidegree rearrangement isomorphism
`(P₁ ⊗ₖ P₂) ⊗_{A₁ ⊗ A₂} (N₁ ⊗ₖ N₂) ≃ₗ[k] (P₁ ⊗_{A₁} N₁) ⊗ₖ (P₂ ⊗_{A₂} N₂)`, sending
`⟦(p₁ ⊗ p₂) ⊗ (n₁ ⊗ n₂)⟧ ↦ ⟦p₁ ⊗ n₁⟧ ⊗ₖ ⟦p₂ ⊗ n₂⟧`. -/
noncomputable def rearrangeBidegree :
    tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂) ≃ₗ[k]
      (tensorOver A₁ N₁ P₁) ⊗[k] (tensorOver A₂ N₂ P₂) :=
  LinearEquiv.ofLinear
    (fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN) (inv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN)
    (LinearMap.ext fun r => by simpa using fwd_inv k A₁ A₂ P₁ P₂ N₁ N₂ hM hN r)
    (LinearMap.ext fun z => by simpa using inv_fwd k A₁ A₂ P₁ P₂ N₁ N₂ hM hN z)

include hM hN in
@[simp] theorem rearrangeBidegree_mk_tmul (p₁ : P₁) (p₂ : P₂) (n₁ : N₁) (n₂ : N₂) :
    rearrangeBidegree k A₁ A₂ P₁ P₂ N₁ N₂ hM hN
        (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ P₂) :=
  fwd_mk_tmul k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ p₂ n₁ n₂

include hM hN in
@[simp] theorem rearrangeBidegree_symm_mk_tmul (p₁ : P₁) (n₁ : N₁) (p₂ : P₂) (n₂ : N₂) :
    (rearrangeBidegree k A₁ A₂ P₁ P₂ N₁ N₂ hM hN).symm
        ((QuotientAddGroup.mk (p₁ ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ P₁)
          ⊗ₜ[k] (QuotientAddGroup.mk (p₂ ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ P₂))
      = (QuotientAddGroup.mk ((p₁ ⊗ₜ[k] p₂) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)) :
          tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (P₁ ⊗[k] P₂)) :=
  inv_mk_tmul_mk k A₁ A₂ P₁ P₂ N₁ N₂ hM hN p₁ n₁ p₂ n₂

end Main

end Etingof

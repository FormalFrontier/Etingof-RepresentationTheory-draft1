import EtingofRepresentationTheory.Chapter8.TensorOverModule
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.TensorProduct.Basic

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
`IsScalarTower k Aᵢ Nᵢ`. This is precisely the "`k → Z(Aᵢ)`" compatibility of the assembler: in the
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
/-- The crux compatibility: `rearrangeAux` sends the external `A₁ ⊗ A₂`-balancing relation on the
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

end Main

end Etingof

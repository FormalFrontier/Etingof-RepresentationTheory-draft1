import EtingofRepresentationTheory.Chapter8.RearrangeBidegreeNat
import EtingofRepresentationTheory.Chapter8.TensorRightFunctorK
import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# The bifunctor natural isomorphism for the `Tor` Künneth rearrangement

Route **step 2** of milestone (c) of the four-fold rearrangement (Problem 8.2.8 `Tor`). Milestones
(a) `Etingof.rearrangeBidegree` (`RearrangeBidegree.lean`) and (b)
`Etingof.rearrangeBidegree_naturality` (`RearrangeBidegreeNat.lean`) provide, for each pair of right
modules `(X, Y)`, a `k`-linear isomorphism

  `tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X⊗ₖY) ≃ₗ[k] (tensorOver A₁ N₁ X) ⊗ₖ (tensorOver A₂ N₂ Y)`

natural in `X` and `Y`. This file packages that data as a **natural isomorphism of bifunctors**

  `rearrangeBifunctorNatIso :`
  `extTensorFunctor ⋙ tensorRightₖ(N₁⊗ₖN₂)  ≅  (tensorRightₖ N₁ · ) ⊗ (tensorRightₖ N₂ · )`

of type `ModuleCat A₁ᵐᵒᵖ ⥤ ModuleCat A₂ᵐᵒᵖ ⥤ ModuleCat k`. The left bifunctor is a post-composition
of the external tensor bifunctor with `Etingof.tensorRightFunctorₖ k (A₁⊗A₂) (N₁⊗ₖN₂)`; the right is
`(X, Y) ↦ (X ⊗_{A₁} N₁) ⊗ₖ (Y ⊗_{A₂} N₂)`, assembled from the two factor functors and the monoidal
tensor on `ModuleCat k`.

Downstream (route step 3, the final construction of the `ChainComplex (ModuleCat k) ℕ` rearrangement
iso) transports this natural iso through `HomologicalComplex.mapBifunctor`.

## Contents

* `extTensorRightFunctor`, `factorTensorFunctor`: the two bifunctors (with the
  restriction-of-scalars `local instance`s on the `ModuleCat` carriers).
* `extModuleK_algebraMap_smul`, `rearrangeSourceEquiv`: the source-diamond reconciliation. The two
  bifunctor objects share the carrier `tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X ⊗[k] Y)` but
  `tensorRightFunctorₖ` equips it with the `k`-action restricted through `(A₁⊗A₂)ᵐᵒᵖ`, whereas
  `rearrangeBidegree` uses the `TensorProduct`-diagonal `k`-action. These agree propositionally (the
  external action of `algebraMap k (A₁⊗A₂)ᵐᵒᵖ c` is `c • ·`), and the identity carrier map reconciles
  the diamond; the target factor `k`-actions already match definitionally.
* `rearrangeBifunctorComponentIso`: milestone (a) `rearrangeBidegree`, retyped to the functor
  objects.
* `rearrangeBifunctorNatIso`: the full bifunctor natural isomorphism, assembled by two nested
  `NatIso.ofComponents`; both naturality squares are the generator computation underlying
  `rearrangeBidegree_naturality` (each factor map is `tensorRightMapₖ`, identified with the
  `tensorOver`-functoriality by `tensorRightMapₖ_eq_tensorOverMapₖ`).
-/

open CategoryTheory MonoidalCategory TensorProduct MulOpposite

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

/-! ### Restriction-of-scalars instances on the `ModuleCat` carriers

The same `local instance`s as `ExternalTensorFunctor.lean` / `TensorRightFunctorK.lean`, brought
into scope so that `(tensorRightFunctorₖ k (A₁⊗A₂) (N₁⊗ₖN₂)).obj (extTensorFunctorObj X Y)` is the
`ModuleCat k` on `tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X⊗ₖY)` with the external action expected by
`rearrangeBidegree`. Stated generically in a `k`-algebra `B` so they cover `A₁`, `A₂` and
`A₁ ⊗[k] A₂` at once. -/

noncomputable local instance instModuleK {B : Type u} [Ring B] [Algebra k B]
    (X : ModuleCat.{u} Bᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k Bᵐᵒᵖ)

local instance instTower {B : Type u} [Ring B] [Algebra k B] (X : ModuleCat.{u} Bᵐᵒᵖ) :
    IsScalarTower k Bᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance instComm {B : Type u} [Ring B] [Algebra k B] (X : ModuleCat.{u} Bᵐᵒᵖ) :
    SMulCommClass k Bᵐᵒᵖ X where
  smul_comm c a m := by
    change (algebraMap k Bᵐᵒᵖ c) • (a • m) = a • ((algebraMap k Bᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action on `X ⊗[k] Y`. Defined as *the very instance*
`extTensorFunctorObj` carries (its carrier is defeq to `X ⊗[k] Y`), so that
`(tensorRightFunctorₖ …).obj (extTensorFunctorObj X Y)` and
`tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X ⊗[k] Y)` share the `(A₁⊗A₂)ᵐᵒᵖ`-action definitionally, dissolving
that half of the `Module`-instance diamond. -/
noncomputable local instance instExtModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) :=
  inferInstanceAs (Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (extTensorFunctorObj k A₁ A₂ X Y))

/-- `k` commutes with the external `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action, because the action is realised by a
`k`-algebra map into `Module.End k (X ⊗[k] Y)`, whose values are `k`-linear endomorphisms. -/
local instance instCommExt (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    SMulCommClass k (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) where
  smul_comm c r m := by
    change c • (extTensorRep k A₁ A₂ X Y r m) = extTensorRep k A₁ A₂ X Y r (c • m)
    rw [map_smul]

/-! ### Bridging `tensorRightMapₖ` with `tensorOverMapₖ ∘ restrictK`

`Etingof.tensorRightFunctorₖ.map f` (for a `ModuleCat Bᵐᵒᵖ`-morphism `f`) and the `k`-linear
functoriality `Etingof.tensorOverMapₖ` used to state milestone (b) both send `⟦m ⊗ n⟧ ↦ ⟦f m ⊗ n⟧`.
This identifies them, letting the NatIso's naturality reduce to `rearrangeBidegree_naturality`. -/

theorem tensorRightMapₖ_eq_tensorOverMapₖ {B : Type u} [Ring B] [Algebra k B]
    (N : Type u) [AddCommGroup N] [Module B N] {M M' : ModuleCat.{u} Bᵐᵒᵖ} (f : M ⟶ M') :
    tensorRightMapₖ k B N f
      = tensorOverMapₖ k B M M' N (restrictK k B M M' f.hom)
          (restrictK_op_smul k B M M' f.hom) := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => simp
  | tmul m n => rw [tensorRightMapₖ_mk, tensorOverMapₖ_mk, restrictK_apply]
  | add a b ha hb => rw [QuotientAddGroup.mk_add, map_add, map_add, ha, hb]

/-! ### The two bifunctors -/

/-- The left bifunctor `(X, Y) ↦ (X ⊗ₖ Y) ⊗_{A₁⊗A₂} (N₁ ⊗ₖ N₂)`: the external tensor bifunctor
post-composed with `tensorRightFunctorₖ k (A₁⊗A₂) (N₁⊗ₖN₂)`. -/
noncomputable def extTensorRightFunctor :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  extTensorFunctor k A₁ A₂ ⋙
    (Functor.whiskeringRight (ModuleCat.{u} A₂ᵐᵒᵖ) (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ)
      (ModuleCat.{u} k)).obj (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))

/-- The right bifunctor `(X, Y) ↦ (X ⊗_{A₁} N₁) ⊗ₖ (Y ⊗_{A₂} N₂)`: the two factor functors
`tensorRightFunctorₖ` combined through the monoidal tensor of `ModuleCat k`. -/
noncomputable def factorTensorFunctor :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  (tensorRightFunctorₖ k A₁ N₁ ⋙ curriedTensor (ModuleCat.{u} k)) ⋙
    (Functor.whiskeringLeft (ModuleCat.{u} A₂ᵐᵒᵖ) (ModuleCat.{u} k) (ModuleCat.{u} k)).obj
      (tensorRightFunctorₖ k A₂ N₂)

/-! ### The component isomorphism -/

include hN in
/-- The component of the natural iso at `(X, Y)`: milestone (a) `rearrangeBidegree`, packaged as an
iso in `ModuleCat k` between the concrete carriers.

The two bifunctor objects `((extTensorRightFunctor …).obj X).obj Y` and
`((factorTensorFunctor …).obj X).obj Y` reduce (by `rfl` at the `Functor.obj` level) to these two
`ModuleCat.of k (tensorOver …)`, **except** that `tensorRightFunctorₖ` equips its `tensorOver` with
the `k`-action restricted through `(A₁⊗A₂)ᵐᵒᵖ` (resp. `Aᵢᵐᵒᵖ`), whereas `rearrangeBidegree` uses the
`TensorProduct`-diagonal `k`-action. These agree propositionally but not definitionally, reconciled
here (an `IsScalarTower` uniqueness / `eqToIso` argument), so this is the retyped milestone-(a)
component. The full bifunctor `NatIso`, assembling these components with naturality from
`rearrangeBidegree_naturality`, is `rearrangeBifunctorNatIso` (defined later in this file). -/
noncomputable def rearrangeComponentIso (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ModuleCat.of k (tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (X ⊗[k] Y))
      ≅ ModuleCat.of k (tensorOver A₁ N₁ X ⊗[k] tensorOver A₂ N₂ Y) :=
  (rearrangeBidegree k A₁ A₂ X Y N₁ N₂
    (extTensorFunctor_op_smul_tmul k A₁ A₂ X Y) hN).toModuleIso

/-! ### Reconciling the source `k`-module diamond -/

/-- On the external tensor `X ⊗[k] Y`, the `k`-action restricted through `(A₁ ⊗[k] A₂)ᵐᵒᵖ` (the one
`tensorRightFunctorₖ k (A₁⊗A₂) (N₁⊗ₖN₂)` puts on its source) coincides with the `TensorProduct`
diagonal `k`-action (the one `rearrangeBidegree` uses): `algebraMap k (A₁⊗A₂)ᵐᵒᵖ c` acts as `c • ·`
because the external representation `extTensorRep` is a `k`-algebra map. This is the source half of
the `Module k` diamond. -/
theorem extModuleK_algebraMap_smul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (c : k)
    (z : X ⊗[k] Y) :
    (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) • z = c • z := by
  change extTensorRep k A₁ A₂ X Y (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) z = c • z
  rw [AlgHom.commutes]
  simp [Module.algebraMap_end_apply]

/-- The source-diamond reconciliation as a `k`-linear equivalence: the identity on the shared
carrier `tensorOver (A₁⊗A₂) (N₁⊗ₖN₂) (X ⊗[k] Y)`, from the functor object's `Module k` (restricted
through `(A₁⊗A₂)ᵐᵒᵖ`) to the `TensorProduct`-diagonal `Module k` used by `rearrangeBidegree`. It is
`k`-linear because the two actions agree on the left factor by `extModuleK_algebraMap_smul`. -/
noncomputable def rearrangeSourceEquiv (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (((extTensorRightFunctor k A₁ A₂ N₁ N₂).obj X).obj Y) ≃ₗ[k]
      tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (X ⊗[k] Y) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' c z := by
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
      simp only [RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul w n =>
          simp only [smul_mk, TensorProduct.smul_tmul']
          exact congrArg (fun v => (QuotientAddGroup.mk (v ⊗ₜ[ℤ] n) :
            tensorOver (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂) (X ⊗[k] Y)))
            (extModuleK_algebraMap_smul k A₁ A₂ X Y c w)
      | add a b ha hb =>
          simp only [QuotientAddGroup.mk_add, smul_add, ha, hb]
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

omit [Module A₁ N₁] [IsScalarTower k A₁ N₁] [Module A₂ N₂] [IsScalarTower k A₂ N₂] in
@[simp] theorem rearrangeSourceEquiv_apply (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    (z : ((extTensorRightFunctor k A₁ A₂ N₁ N₂).obj X).obj Y) :
    rearrangeSourceEquiv k A₁ A₂ N₁ N₂ X Y z = z := rfl

/-! ### The bifunctor component isomorphism -/

include hN in
/-- The component of the bifunctor natural isomorphism at `(X, Y)`, as a `k`-linear equivalence
between the actual functor objects: reconcile the source `k`-module diamond
(`rearrangeSourceEquiv`), then apply milestone (a) `rearrangeBidegree`. The target already matches
the functor object definitionally (the factor `k`-actions agree). -/
noncomputable def rearrangeComponentLinEquiv (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (((extTensorRightFunctor k A₁ A₂ N₁ N₂).obj X).obj Y) ≃ₗ[k]
      (((factorTensorFunctor k A₁ A₂ N₁ N₂).obj X).obj Y) :=
  (rearrangeSourceEquiv k A₁ A₂ N₁ N₂ X Y).trans
    (rearrangeBidegree k A₁ A₂ X Y N₁ N₂ (extTensorFunctor_op_smul_tmul k A₁ A₂ X Y) hN)

include hN in
@[simp] theorem rearrangeComponentLinEquiv_mk (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (x : X) (y : Y) (n₁ : N₁) (n₂ : N₂) :
    rearrangeComponentLinEquiv k A₁ A₂ N₁ N₂ hN X Y
        (QuotientAddGroup.mk ((x ⊗ₜ[k] y) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (x ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ X)
          ⊗ₜ[k] (QuotientAddGroup.mk (y ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ Y) := by
  rw [rearrangeComponentLinEquiv, LinearEquiv.trans_apply]
  exact rearrangeBidegree_mk_tmul k A₁ A₂ X Y N₁ N₂
    (extTensorFunctor_op_smul_tmul k A₁ A₂ X Y) hN x y n₁ n₂

include hN in
/-- The component of the bifunctor natural isomorphism at `(X, Y)`, as an iso in `ModuleCat k`
between the actual functor objects. -/
noncomputable def rearrangeBifunctorComponentIso (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ((extTensorRightFunctor k A₁ A₂ N₁ N₂).obj X).obj Y ≅
      ((factorTensorFunctor k A₁ A₂ N₁ N₂).obj X).obj Y :=
  (rearrangeComponentLinEquiv k A₁ A₂ N₁ N₂ hN X Y).toModuleIso

include hN in
@[simp] theorem rearrangeBifunctorComponentIso_hom_apply (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (x : X) (y : Y) (n₁ : N₁) (n₂ : N₂) :
    (rearrangeBifunctorComponentIso k A₁ A₂ N₁ N₂ hN X Y).hom
        (QuotientAddGroup.mk ((x ⊗ₜ[k] y) ⊗ₜ[ℤ] (n₁ ⊗ₜ[k] n₂)))
      = (QuotientAddGroup.mk (x ⊗ₜ[ℤ] n₁) : tensorOver A₁ N₁ X)
          ⊗ₜ[k] (QuotientAddGroup.mk (y ⊗ₜ[ℤ] n₂) : tensorOver A₂ N₂ Y) :=
  rearrangeComponentLinEquiv_mk k A₁ A₂ N₁ N₂ hN X Y x y n₁ n₂

omit [Module A₁ N₁] [IsScalarTower k A₁ N₁] [Module A₂ N₂] [IsScalarTower k A₂ N₂] in
theorem extTensorRightFunctor_obj_map (X : ModuleCat.{u} A₁ᵐᵒᵖ) {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') :
    ((extTensorRightFunctor k A₁ A₂ N₁ N₂).obj X).map g =
      (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).map (extTensorFunctorMap k (𝟙 X) g) :=
  rfl

omit [Module k N₁] [IsScalarTower k A₁ N₁] [Module k N₂] [IsScalarTower k A₂ N₂] instN in
theorem factorTensorFunctor_obj_map (X : ModuleCat.{u} A₁ᵐᵒᵖ) {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') :
    ((factorTensorFunctor k A₁ A₂ N₁ N₂).obj X).map g =
      MonoidalCategory.whiskerLeft ((tensorRightFunctorₖ k A₁ N₁).obj X)
        ((tensorRightFunctorₖ k A₂ N₂).map g) :=
  rfl

/-- `rfl` restatement of `extTensorFunctorMapHom_tmul` in this file's instance context (the
`Module k` on the carriers is `instModuleK`, syntactically distinct from `ExternalTensorFunctor`'s
private `restrictModule₁`, so the imported simp lemma does not fire). -/
theorem extMapHom_tmul {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    extTensorFunctorMapHom k f g (x ⊗ₜ[k] y) = f.hom x ⊗ₜ[k] g.hom y :=
  rfl

omit [Module A₁ N₁] [IsScalarTower k A₁ N₁] [Module A₂ N₂] [IsScalarTower k A₂ N₂] in
theorem extTensorRightFunctor_map_app {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} (f : X ⟶ X')
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ((extTensorRightFunctor k A₁ A₂ N₁ N₂).map f).app Y =
      (tensorRightFunctorₖ k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)).map (extTensorFunctorMap k f (𝟙 Y)) :=
  rfl

omit [Module k N₁] [IsScalarTower k A₁ N₁] [Module k N₂] [IsScalarTower k A₂ N₂] instN in
theorem factorTensorFunctor_map_app {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} (f : X ⟶ X')
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    ((factorTensorFunctor k A₁ A₂ N₁ N₂).map f).app Y =
      MonoidalCategory.whiskerRight ((tensorRightFunctorₖ k A₁ N₁).map f)
        ((tensorRightFunctorₖ k A₂ N₂).obj Y) :=
  rfl

/-! ### The bifunctor natural isomorphism -/

include hN in
/-- The natural isomorphism of functors
`(extTensorRightFunctor).obj X ≅ (factorTensorFunctor).obj X` (naturality in the second variable
`Y`), for a fixed first variable `X`. Kept as a named `def` so the large naturality proof stays
opaque to the outer naturality proof. -/
noncomputable def rearrangeBifunctorNatIsoApp (X : ModuleCat.{u} A₁ᵐᵒᵖ) :
    (extTensorRightFunctor k A₁ A₂ N₁ N₂).obj X ≅ (factorTensorFunctor k A₁ A₂ N₁ N₂).obj X :=
  NatIso.ofComponents
    (fun Y => rearrangeBifunctorComponentIso k A₁ A₂ N₁ N₂ hN X Y)
    (by
      intro Y Y' g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [QuotientAddGroup.mk_add, map_add, ha, hb]
      | tmul p q =>
          induction p using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb =>
              simp only [add_tmul, QuotientAddGroup.mk_add, map_add, ha, hb]
          | tmul x y =>
              induction q using TensorProduct.induction_on with
              | zero => simp
              | add a b ha hb =>
                  simp only [tmul_add, QuotientAddGroup.mk_add, map_add, ha, hb]
              | tmul n₁ n₂ =>
                  simp only [extTensorRightFunctor_obj_map, factorTensorFunctor_obj_map,
                    ModuleCat.comp_apply]
                  erw [tensorRightFunctorₖ_map_mk]
                  erw [extTensorFunctorMap_hom, extMapHom_tmul]
                  simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq]
                  rw [rearrangeBifunctorComponentIso_hom_apply,
                    rearrangeBifunctorComponentIso_hom_apply]
                  erw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
                  rw [tensorRightFunctorₖ_map_mk])

include hN in
@[simp] theorem rearrangeBifunctorNatIsoApp_hom_app (X : ModuleCat.{u} A₁ᵐᵒᵖ)
    (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (rearrangeBifunctorNatIsoApp k A₁ A₂ N₁ N₂ hN X).hom.app Y =
      (rearrangeBifunctorComponentIso k A₁ A₂ N₁ N₂ hN X Y).hom :=
  rfl

include hN in
/-- **The bifunctor natural isomorphism.** The natural isomorphism of bifunctors
`extTensorRightFunctor ≅ factorTensorFunctor`, i.e.
`(X, Y) ↦ (X ⊗ₖ Y) ⊗_{A₁⊗A₂} (N₁ ⊗ₖ N₂)` is naturally isomorphic to
`(X, Y) ↦ (X ⊗_{A₁} N₁) ⊗ₖ (Y ⊗_{A₂} N₂)`. The components are `rearrangeBifunctorComponentIso`
(milestone (a) `rearrangeBidegree` after reconciling the source `Module k` diamond); naturality in
each variable is the generator computation underlying `rearrangeBidegree_naturality`. -/
noncomputable def rearrangeBifunctorNatIso :
    extTensorRightFunctor k A₁ A₂ N₁ N₂ ≅ factorTensorFunctor k A₁ A₂ N₁ N₂ :=
  NatIso.ofComponents
    (fun X => rearrangeBifunctorNatIsoApp k A₁ A₂ N₁ N₂ hN X)
    (by
      intro X X' f
      apply NatTrans.ext
      apply funext
      intro Y
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [QuotientAddGroup.mk_add, map_add, ha, hb]
      | tmul p q =>
          induction p using TensorProduct.induction_on with
          | zero => simp
          | add a b ha hb =>
              simp only [add_tmul, QuotientAddGroup.mk_add, map_add, ha, hb]
          | tmul x y =>
              induction q using TensorProduct.induction_on with
              | zero => simp
              | add a b ha hb =>
                  simp only [tmul_add, QuotientAddGroup.mk_add, map_add, ha, hb]
              | tmul n₁ n₂ =>
                  simp only [NatTrans.comp_app, rearrangeBifunctorNatIsoApp_hom_app,
                    extTensorRightFunctor_map_app, factorTensorFunctor_map_app,
                    ModuleCat.comp_apply]
                  erw [tensorRightFunctorₖ_map_mk]
                  erw [extTensorFunctorMap_hom, extMapHom_tmul]
                  simp only [ModuleCat.hom_id, LinearMap.id_coe, id_eq]
                  rw [rearrangeBifunctorComponentIso_hom_apply,
                    rearrangeBifunctorComponentIso_hom_apply]
                  erw [ModuleCat.MonoidalCategory.whiskerRight_apply]
                  rw [tensorRightFunctorₖ_map_mk])

end Etingof

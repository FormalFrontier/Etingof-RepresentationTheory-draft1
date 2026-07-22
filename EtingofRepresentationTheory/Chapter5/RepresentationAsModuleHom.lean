import Mathlib

/-!
# `asModule` transfer utilities for `Representation`

General-purpose `MonoidAlgebra k G`-module lemmas for `Representation.asModule`,
extracted from `PolynomialGLDecomposition.lean` so that consumers needing only
these utilities (e.g. `CauchyDetQuotientGrading.asModuleHomOfIntertwiner`) do not
inherit the Schur-Weyl import closure of the decomposition file — which
transitively reaches `DetInvElim` and would otherwise create an import cycle with
the determinant-quotient assembly (issue #5108, parent #5076).

These are pure representation-theory facts (no Schur-Weyl, no `DetInvElim`):

* `single_smul_directSum`, `asModule_directSum_equiv` — glue-A (#4714): the
  `asModule` of a `Representation.directSum` splits as a `DirectSum` of the
  component `asModule`s.
* `tprodSplitEquiv`, `asModule_trivial_tprod_equiv` — glue-B (#4715): a
  trivial-tensor representation `(trivial S).tprod σ` splits into `dim S` copies
  of `asModule σ`.
* `asModuleHomOfIntertwiner`, `asModuleEquivOfIntertwiner` — lift a `k`-linear
  intertwiner / equivalence to a `MonoidAlgebra k G`-linear map / equivalence of
  `asModule`s.
-/

open scoped TensorProduct DirectSum

namespace Representation

section DirectSumAsModule

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {ι : Type*} {V : ι → Type*}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]

/-- The componentwise `MonoidAlgebra k G`-action of `single g t` on a direct sum
of `asModule`s collapses to the scalar `t` times the `DirectSum.lmap` of the
per-component `ρs i g`. Stated with a genuinely target-typed argument `y` so the
`single g t • y` resolves to the `DirectSum` action (not a poisoned `asModule`
action), which is what makes the componentwise `single_smul` rewrite apply. -/
theorem single_smul_directSum (ρs : (i : ι) → Representation k G (V i))
    (g : G) (t : k) (y : DirectSum ι (fun i => Representation.asModule (ρs i))) :
    MonoidAlgebra.single g t • y = t • DirectSum.lmap (fun i => ρs i g) y := by
  refine DirectSum.ext (β := fun i => Representation.asModule (ρs i)) fun i => ?_
  rw [DirectSum.smul_apply, Representation.single_smul]
  rfl

/-- The `MonoidAlgebra k G`-linear equivalence identifying the `asModule` of a
direct sum of representations with the direct sum of their `asModule`s.

This is the keystone conversion for the Schur-Weyl Step E assembly (#4667): the
decomposition target is a `DirectSum` of `asModule`s, which is *not* itself the
`asModule` of a single representation, so the equivariant embedding (a
`MonoidAlgebra k G`-linear map into `asModule (directSum ρs)`) must be retargeted
through this equiv.

Both carriers are defeq to `⨁ i, V i`, so the underlying map is the identity;
only compatibility of the two `MonoidAlgebra k G`-actions needs proof, which
reduces componentwise to `Representation.single_smul` after a
`MonoidAlgebra.induction_linear` on the scalar. -/
noncomputable def asModule_directSum_equiv (ρs : (i : ι) → Representation k G (V i)) :
    Representation.asModule (Representation.directSum ρs) ≃ₗ[MonoidAlgebra k G]
      DirectSum ι (fun i => Representation.asModule (ρs i)) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_smul, ha, hb]
    | single g t =>
      rw [single_smul_directSum, Representation.single_smul, Representation.directSum_apply]
      rfl

end DirectSumAsModule

section TrivialTprodSplit

open scoped TensorProduct
open TensorProduct

variable {k G S W : Type*} [CommRing k] [Monoid G]
variable [AddCommGroup S] [Module k S] [AddCommGroup W] [Module k W]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The underlying `k`-linear splitting `S ⊗[k] W ≃ ⨁_β W` determined by a basis
`b` of `S`: a pure tensor `s ⊗ w` is sent to the family `j ↦ b.repr s j • w`.

Composition of `b.repr` (turning `S` into `β →₀ k`), `finsuppScalarLeft`
(absorbing the `Finsupp` into the right factor), the finite `Finsupp ≃ Pi`, and
`DirectSum ≃ Pi` for the `Fintype` index. -/
noncomputable def tprodSplitEquiv (b : Module.Basis β k S) :
    S ⊗[k] W ≃ₗ[k] DirectSum β (fun _ => W) :=
  TensorProduct.congr b.repr (LinearEquiv.refl k W) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k W β ≪≫ₗ
      Finsupp.linearEquivFunOnFinite k W β ≪≫ₗ
        (DirectSum.linearEquivFunOnFintype k β (fun _ => W)).symm

/-- The `Pi`-coordinate form of `tprodSplitEquiv` on a pure tensor. -/
theorem linearEquivFunOnFintype_tprodSplitEquiv_tmul (b : Module.Basis β k S)
    (s : S) (w : W) :
    (DirectSum.linearEquivFunOnFintype k β (fun _ => W)) (tprodSplitEquiv (W := W) b (s ⊗ₜ[k] w))
      = fun i => b.repr s i • w := by
  simp only [tprodSplitEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  funext i
  simp [Finsupp.linearEquivFunOnFinite_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply]

/-- The `i`-th component of `tprodSplitEquiv` on a pure tensor. -/
@[simp]
theorem tprodSplitEquiv_tmul_apply (b : Module.Basis β k S) (s : S) (w : W) (i : β) :
    tprodSplitEquiv (W := W) b (s ⊗ₜ[k] w) i = b.repr s i • w := by
  have := congrFun (linearEquivFunOnFintype_tprodSplitEquiv_tmul b s w) i
  simpa using this

/-- `tprodSplitEquiv` intertwines the trivial-tensor action `(trivial S).tprod σ`
with the componentwise action `directSum (fun _ : β => σ)`: on the `S`-factor the
action is the identity, so under the basis splitting each coordinate carries an
independent copy of `σ`. -/
theorem tprodSplitEquiv_intertwines (b : Module.Basis β k S) (σ : Representation k G W)
    (g : G) (x : S ⊗[k] W) :
    tprodSplitEquiv b (((Representation.trivial k G S).tprod σ) g x)
      = (Representation.directSum (V := fun _ => W) (fun _ : β => σ)) g (tprodSplitEquiv b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.trivial_apply]
    refine DirectSum.ext (β := fun _ : β => W) fun i => ?_
    rw [tprodSplitEquiv_tmul_apply, Representation.directSum_apply, DirectSum.lmap_apply,
      tprodSplitEquiv_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The `MonoidAlgebra k G`-linear carrier identification underlying glue-B, before
the final `asModule`-splitting: `asModule ((trivial S).tprod σ) ≃ asModule` of the
direct-sum representation `directSum (fun _ : β => σ)`. The carrier map is
`tprodSplitEquiv`; equivariance reduces to `tprodSplitEquiv_intertwines` via
`single_smul`. -/
noncomputable def asModule_trivial_tprod_equiv_aux (b : Module.Basis β k S)
    (σ : Representation k G W) :
    Representation.asModule ((Representation.trivial k G S).tprod σ) ≃ₗ[MonoidAlgebra k G]
      Representation.asModule (Representation.directSum (V := fun _ => W) (fun _ : β => σ)) where
  toFun := tprodSplitEquiv b
  invFun := (tprodSplitEquiv b).symm
  map_add' := map_add _
  left_inv := (tprodSplitEquiv b).left_inv
  right_inv := (tprodSplitEquiv b).right_inv
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a c ha hc => simp only [add_smul, map_add, ha, hc]
    | single g t =>
      rw [Representation.single_smul, Representation.single_smul, map_smul]
      simp only [Representation.asModuleEquiv]
      congr 1
      exact tprodSplitEquiv_intertwines b σ g _

/-- **glue-B (#4715).** Splitting a trivial-tensor representation into copies: as a
`MonoidAlgebra k G`-module, `asModule ((trivial k G S).tprod σ)` is the direct sum,
indexed by a basis `b` of `S`, of `dim S` copies of `asModule σ`.

The `GL_N`-action is trivial on the `S`-factor (`trivial S`), so under the basis
splitting `S ⊗ W ≃ ⨁_β W` (`tprodSplitEquiv`) the action becomes the componentwise
copy of `σ` (`asModule_trivial_tprod_equiv_aux`); glue-A
(`asModule_directSum_equiv`, #4714) then splits that `asModule` of a
`Representation.directSum` into the `DirectSum` of the component `asModule`s. -/
noncomputable def asModule_trivial_tprod_equiv (b : Module.Basis β k S)
    (σ : Representation k G W) :
    Representation.asModule ((Representation.trivial k G S).tprod σ) ≃ₗ[MonoidAlgebra k G]
      DirectSum β (fun _ => Representation.asModule σ) :=
  asModule_trivial_tprod_equiv_aux b σ ≪≫ₗ
    asModule_directSum_equiv (ι := β) (V := fun _ => W) (fun _ : β => σ)

end TrivialTprodSplit

section Intertwiner

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {V W : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- A `k`-linear map intertwining representations `ρ` and `σ` lifts to a
`MonoidAlgebra k G`-linear map between their `asModule`s (the underlying function is
unchanged). The compatibility with the `MonoidAlgebra` action reduces, via
`MonoidAlgebra.induction_linear`, to the intertwining hypothesis on `single g t`. -/
def asModuleHomOfIntertwiner {ρ : Representation k G V} {σ : Representation k G W}
    (f : V →ₗ[k] W) (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) :
    Representation.asModule ρ →ₗ[MonoidAlgebra k G] Representation.asModule σ where
  toFun := f
  map_add' := map_add f
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | single g t =>
      rw [Representation.single_smul, Representation.single_smul, map_smul]
      simp only [Representation.asModuleEquiv]
      congr 1
      exact hf g _

@[simp] theorem asModuleHomOfIntertwiner_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : V →ₗ[k] W)
    (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) (x : Representation.asModule ρ) :
    asModuleHomOfIntertwiner f hf x = f x := rfl

/-- A `k`-linear equivalence intertwining `ρ` and `σ` lifts to a
`MonoidAlgebra k G`-linear equivalence between their `asModule`s. -/
def asModuleEquivOfIntertwiner {ρ : Representation k G V} {σ : Representation k G W}
    (f : V ≃ₗ[k] W) (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) :
    Representation.asModule ρ ≃ₗ[MonoidAlgebra k G] Representation.asModule σ where
  toFun := f
  invFun := f.symm
  map_add' := map_add f
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | single g t =>
      rw [Representation.single_smul, Representation.single_smul, map_smul]
      simp only [Representation.asModuleEquiv]
      congr 1
      exact hf g _

@[simp] theorem asModuleEquivOfIntertwiner_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : V ≃ₗ[k] W)
    (hf : ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)) (x : Representation.asModule ρ) :
    asModuleEquivOfIntertwiner f hf x = f x := rfl

end Intertwiner

end Representation

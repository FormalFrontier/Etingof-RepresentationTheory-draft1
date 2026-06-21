import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer
import EtingofRepresentationTheory.Chapter5.PolynomialRepEmbedding
import EtingofRepresentationTheory.Chapter5.SemisimpleIsotypic

/-!
# Schur-Weyl #5, Step E: a polynomial `GL_N`-rep is a direct sum of abstract simples

This file assembles the *equivariant complete reducibility* of a polynomial
`GL_N(k)`-representation (Etingof §5.23, issue #2482). The main result,
`decompose_polynomial_gl_rep`, says that a finite-dimensional algebraic
`GL_N(k)`-representation `M`, all of whose weights have degree `n`, decomposes
`GL_N`-equivariantly (i.e. as a `MonoidAlgebra k GL_N`-module) as a finite
direct sum of the **abstract simple summands `L i`** of `V^{⊗n}`
(`V = Fin N → k`).

## Abstract-summand form (resolves the circularity with #6)

The decomposition is stated in terms of the abstract `L i` of the Schur-Weyl
decomposition of `V^{⊗n}` (`glTensorRep_equivariant_schurWeyl_decomposition`),
*not* in terms of concrete `SchurModule k N λ`. The concrete identification
`L i ≅ SchurModule k N λ` is the highest-weight classification that the
consumer #6 (`iso_of_formalCharacter_eq_schurPoly`) needs; routing it there
keeps the dependency graph acyclic (see the analysis recorded on issue #2482
and in `FormalCharacterIso.lean:1053`).

## Proof structure

The assembly composes three already-merged pieces with two bridge lemmas:

* **#4598** `polynomial_homog_rep_equivariant_embedding` — the `GL_N`-equivariant
  `k`-linear embedding `M ↪ (V^{⊗n})^m`.
* **#4600** `submodule_of_directSum_simple_iso_directSum` — a submodule of a
  finite direct sum of simple `R`-modules is itself a direct sum of those
  simples.
* `glTensorRep_equivariant_schurWeyl_decomposition` (equivariance) and
  `Theorem5_18_4_GL_rep_decomposition_simple` (simplicity of each `L i`).

The two named decomposition theorems build the **same** `L i = FDRep.of ρ_i`
but expose disjoint clauses (one the equivariance, the other the simplicity).
Unifying them, and transferring the `k`-linear equivariant data to the
`MonoidAlgebra k GL_N`-module level expected by the isotypic engine, are the
two bridge lemmas proved here:

* `glTensorRep_schurWeyl_decomposition_equivariant_simple` — the unified
  equivariant + simple decomposition (merges the two existing proofs, both over
  `FDRep.of ρ_i`).
* `polynomial_homog_rep_asModule_embeds_directSum_simple` (#4716) — packages
  #4598 + the unified decomposition + the `asModule` transfer
  (`asModuleHomOfIntertwiner` / `asModuleEquivOfIntertwiner`) + glue-A (#4714)
  + glue-B (#4715) + the `Fin m`-fold product and sigma flattening into a
  single injective `R`-linear embedding of `M.asModule` as a submodule of a
  finite direct sum of the simple `L i`.

Given those two, `decompose_polynomial_gl_rep` is a clean application of the
isotypic engine #4600.
-/

open scoped TensorProduct DirectSum
open CategoryTheory

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
  simp [Finsupp.linearEquivFunOnFinite_apply, finsuppScalarLeft_apply_tmul_apply]

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

namespace Etingof.PolynomialGLDecomposition

universe u

variable (k : Type u) [Field k] (N : ℕ)

/-- Abbreviation for the group algebra of `GL_N(k)`, the ring over which the
`GL_N`-equivariant decompositions are stated. -/
abbrev GLAlg := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Unified equivariant + simple Schur-Weyl decomposition of `V^{⊗n}`.**

This is `glTensorRep_equivariant_schurWeyl_decomposition`
(`FormalCharacterIso.lean:775`) strengthened with the simplicity clause of
`Theorem5_18_4_GL_rep_decomposition_simple` (`SchurWeylGLTransfer.lean:659`):
each abstract summand `L i` is *simple* as a `MonoidAlgebra k GL_N`-module.

Both source theorems are built from the same explicit bimodule decomposition
(`Theorem5_18_4_bimodule_decomposition_explicit`) and produce the *same*
`L i = FDRep.of ρ_i` with `ρ_i = (postCompCentralizerMonoidHom …).comp glHom`.
The proof therefore re-runs the equivariance computation of the former while
keeping the centralizer-side simplicity clause that
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` transports to `GL_N`.

Built by destructuring `Theorem5_18_4_bimodule_decomposition_explicit` once
(keeping both its centralizer-side simplicity clause `homA_simp` and its
evaluation formula `he`), reconstructing the `GL_N`-action `ρ_i` exactly as
`Theorem5_18_4_GL_rep_decomposition_explicit`, then assembling the equivariance
(à la `glTensorRep_equivariant_schurWeyl_decomposition`) and the per-`L i`
simplicity (à la `Theorem5_18_4_GL_rep_decomposition_simple`'s `hL_simple`) over
that one shared `ρ_i`. -/
theorem glTensorRep_schurWeyl_decomposition_equivariant_simple
    [IsAlgClosed k] [CharZero k] (n : ℕ) (hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (GLAlg k N) (Representation.asModule (L i).ρ)),
      ∃ (e : TensorPower k (Fin N → k) n ≃ₗ[k]
          (DirectSum ι (fun i => S i ⊗[k] (L i : Type u)))),
        ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v) := by
  classical
  -- The combined explicit + simple decomposition supplies, over one shared
  -- `ρ_i`, the simplicity clause AND the explicit equivariance ingredients
  -- (the iso `e` already typed in the `(L i : Type u)` family, the evaluation
  -- formula `he`, and the action formula `h_act`).
  obtain ⟨ι, hιFin, hιDec, S', hS'_simp, hS'_dist, hSi_fin, L, hL_simple,
      L_carrier, e, he, h_act⟩ :=
    Theorem5_18_4_GL_rep_decomposition_explicit_simple k N n hN
  refine ⟨ι, hιFin, hιDec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance,
    fun i => hSi_fin i, L, hL_simple, ?_, ?_⟩
  · exact e
  intro g v
  -- Reduce equivariance to: (glTensorRep g) ∘ e.symm = e.symm ∘ directSum_action g.
  have h_lin :
      (glTensorRep k N n g) ∘ₗ (e.symm : _ →ₗ[k] _) =
        (e.symm : _ →ₗ[k] _) ∘ₗ
          (Representation.directSum (fun i =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (↥(S' i))).tprod (L i).ρ) g) := by
    refine DirectSum.linearMap_ext k fun i => ?_
    apply TensorProduct.ext'
    intro s l
    change (glTensorRep k N n g) (e.symm
        (DirectSum.lof k ι (fun i => ↥(S' i) ⊗[k] (L i : Type u)) i
          (s ⊗ₜ[k] l))) =
      e.symm ((Representation.directSum (fun i =>
        (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
          (↥(S' i))).tprod (L i).ρ) g)
        (DirectSum.lof k ι _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lof_eq_of, he i s l]
    change _ = e.symm (DirectSum.lmap
      (fun i => ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (DirectSum.of _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lmap_of, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, he i s ((L i).ρ g l)]
    exact (h_act i g l s).symm
  have h := LinearMap.congr_fun h_lin (e v)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [show (e.symm : _ →ₗ[k] _) (e v) = v from e.symm_apply_apply v] at h
  rw [show (e.symm : _ →ₗ[k] _) ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) =
    e.symm ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) from rfl] at h
  exact (LinearEquiv.eq_symm_apply e).mp h

/-- **`M` embeds `R`-linearly as a submodule of a finite direct sum of the
abstract simple summands `L i`.**

Bundles three steps into the single form consumed by the isotypic engine:

1. `polynomial_homog_rep_equivariant_embedding` (#4598): the `GL_N`-equivariant
   `k`-linear embedding `M ↪ (V^{⊗n})^m`.
2. `glTensorRep_schurWeyl_decomposition_equivariant_simple`: the ambient
   `V^{⊗n}` (hence `(V^{⊗n})^m`) decomposes equivariantly into the simple
   `L i`, with multiplicities (each `S i ⊗ L i` is `dim(S i)` copies of `L i`).
3. The `asModule` transfer: a `GL_N`-equivariant `k`-linear map is exactly a
   `MonoidAlgebra k GL_N`-linear map between the `asModule`s.

The output exposes an index `κ`, a map `g : κ → ι` recording which simple each
ambient summand is, an `R`-linear identification `e` of the ambient
`(V^{⊗n})^m`-module with `⨁_{c : κ} asModule (L (g c))`, and a submodule `M'`
of that ambient module together with an `R`-linear iso `asModule M.ρ ≃ M'`.

The hypothesis `h_span` — that the `ℕ`-indexed weight spaces span `M` — is
**essential** (it says `M` is genuinely *polynomial*, not merely algebraic). It
feeds `polynomial_homog_rep_equivariant_embedding` (#4598); without it the
statement is false, since `IsAlgebraicRepresentation` + `h_homog` admits the
counterexample `M = Sym²(V) ⊗ det⁻¹` (`N = 2`, `n = 0`), which has no embedding
into `V^{⊗0}`. -/
theorem polynomial_homog_rep_asModule_embeds_directSum_simple
    [IsAlgClosed k] [CharZero k] (n : ℕ) (hN : n ≤ N)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (GLAlg k N) (Representation.asModule (L i).ρ))
      (κ : Type) (_ : Finite κ) (gκ : κ → ι)
      (W : Type u) (_ : AddCommGroup W) (_ : Module (GLAlg k N) W)
      (_ : W ≃ₗ[GLAlg k N]
        DirectSum κ (fun c => Representation.asModule (L (gκ c)).ρ))
      (M' : Submodule (GLAlg k N) W),
      Nonempty (Representation.asModule M.ρ ≃ₗ[GLAlg k N] M') := by
  classical
  -- (1) #4598: a `GL_N`-equivariant `k`-linear embedding `M ↪ (V^{⊗n})^m`.
  obtain ⟨m, φ, hφinj, hφeq⟩ :=
    Etingof.PolynomialRepEmbedding.polynomial_homog_rep_equivariant_embedding
      (M := M) (halg := halg) (h_span := h_span) (h_homog := h_homog)
  -- (2) unified equivariant + simple Schur–Weyl decomposition of `V^{⊗n}`.
  obtain ⟨ι, hιFin, hιDec, S, hSacg, hSmod, hSfin, L, hLsimp, e, he⟩ :=
    glTensorRep_schurWeyl_decomposition_equivariant_simple (k := k) (N := N) n hN
  haveI iSfree : ∀ i, Module.Free k (S i) := fun i => Module.Free.of_divisionRing k (S i)
  -- basis index of each multiplicity space, in `Type 0` so `κ` stays small.
  set β : ι → Type := fun i => Fin (Module.finrank k (S i)) with hβ
  -- (3) view `φ` as a `k`-linear map into the `DirectSum` over the finite index `Fin m`.
  set piToDS := (DirectSum.linearEquivFunOnFintype k (Fin m)
    (fun _ : Fin m => TensorPower k (Fin N → k) n)).symm with hpiToDS
  set φ' : (M : Type u) →ₗ[k]
      DirectSum (Fin m) (fun _ : Fin m => TensorPower k (Fin N → k) n) :=
    piToDS.toLinearMap ∘ₗ φ with hφ'
  have hφ'inj : Function.Injective φ' := piToDS.injective.comp hφinj
  have hcoe : ∀ (w : Fin m → TensorPower k (Fin N → k) n) (a : Fin m),
      (piToDS w) a = w a := by intro w a; rw [hpiToDS]; rfl
  -- equivariance of `φ'` for the `Fin m`-fold `directSum` of `glTensorRep`.
  have hφ'eq : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : (M : Type u)),
      φ' (M.ρ g x) =
        Representation.directSum (fun _ : Fin m => glTensorRep k N n) g (φ' x) := by
    intro g x
    refine DFinsupp.ext fun a => ?_
    rw [show φ' (M.ρ g x) = piToDS (φ (M.ρ g x)) from rfl,
        show φ' x = piToDS (φ x) from rfl, hcoe,
        Representation.directSum_apply, DirectSum.lmap_apply, hcoe, hφeq]
    simp only [Matrix.toLin'_apply']
    rfl
  -- (4) transfer `φ'` to a `MonoidAlgebra k G`-linear (injective) map on `asModule`s.
  let φR : Representation.asModule M.ρ →ₗ[GLAlg k N]
      Representation.asModule (Representation.directSum (fun _ : Fin m => glTensorRep k N n)) :=
    Representation.asModuleHomOfIntertwiner φ' hφ'eq
  have hφRinj : Function.Injective φR := hφ'inj
  -- (5) decompose the ambient `asModule` into the simple summands `L i`.
  let Einner :
      Representation.asModule (glTensorRep k N n) ≃ₗ[GLAlg k N]
        DirectSum (Σ i : ι, β i) (fun ν => Representation.asModule (L ν.1).ρ) :=
    (Representation.asModuleEquivOfIntertwiner e he) ≪≫ₗ
      (Representation.asModule_directSum_equiv
        (fun i => (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k) (S i)).tprod (L i).ρ)) ≪≫ₗ
      (DFinsupp.mapRange.linearEquiv (fun i =>
        Representation.asModule_trivial_tprod_equiv (Module.finBasis k (S i)) (L i).ρ)) ≪≫ₗ
      (DirectSum.sigmaLcurryEquiv (R := GLAlg k N)
        (δ := fun (i : ι) (_ : β i) => Representation.asModule (L i).ρ)).symm
  let E1 := Representation.asModule_directSum_equiv (fun _ : Fin m => glTensorRep k N n)
  let E2 := DFinsupp.mapRange.linearEquiv (fun _ : Fin m => Einner)
  let Eouter := (DirectSum.sigmaLcurryEquiv (R := GLAlg k N)
    (δ := fun (_ : Fin m) (ν : Σ i : ι, β i) => Representation.asModule (L ν.1).ρ)).symm
  -- the full injective `R`-linear map into `⨁_κ asModule (L (gκ c)).ρ`.
  let ψ := (Eouter.toLinearMap ∘ₗ E2.toLinearMap ∘ₗ E1.toLinearMap) ∘ₗ φR
  have hψinj : Function.Injective ψ :=
    ((Eouter.injective.comp E2.injective).comp E1.injective).comp hφRinj
  refine ⟨ι, hιFin, hιDec, L, hLsimp,
    (Σ _ : Fin m, Σ i : ι, β i), inferInstance, (fun c => c.2.1),
    DirectSum (Σ _ : Fin m, Σ i : ι, β i) (fun c => Representation.asModule (L c.2.1).ρ),
    inferInstance, inferInstance, LinearEquiv.refl (GLAlg k N) _,
    LinearMap.range ψ, ⟨LinearEquiv.ofInjective ψ hψinj⟩⟩

/-- **A polynomial `GL_N`-representation is a direct sum of abstract simple
summands of `V^{⊗n}`** (Schur-Weyl #5, Step E, issue #2482).

Let `M` be a finite-dimensional algebraic `GL_N(k)`-representation all of whose
weight spaces are concentrated in total degree `n`. Then `M` decomposes, as a
`MonoidAlgebra k GL_N`-module (i.e. `GL_N`-equivariantly), as a finite direct
sum of the abstract simple summands `L i` of `V^{⊗n}`:
`M.asModule ≃ ⨁_{j : Fin p} (L (f j)).asModule`.

Reading off `mult i := Nat.card {j // f j = i}` recovers the
multiplicity-indexed form `M ≅ ⨁_i (Fin (mult i) → L i)`. The decomposition is
stated for the *abstract* `L i` (not concrete Schur modules) to keep the
dependency graph with the consumer #6 acyclic. -/
theorem decompose_polynomial_gl_rep
    [IsAlgClosed k] [CharZero k] (n : ℕ) (hN : n ≤ N)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (GLAlg k N) (Representation.asModule (L i).ρ))
      (p : ℕ) (f : Fin p → ι),
      Nonempty (Representation.asModule M.ρ ≃ₗ[GLAlg k N]
        DirectSum (Fin p) (fun j => Representation.asModule (L (f j)).ρ)) := by
  classical
  -- Embed `M.asModule` as a submodule `M'` of an ambient module `W` that is
  -- `R`-linearly a finite direct sum of the simple `L (gκ c)`.
  obtain ⟨ι, hιFin, hιDec, L, hLsimp, κ, hκFin, gκ, W, hWacg, hWmod, e, M', ⟨eM⟩⟩ :=
    polynomial_homog_rep_asModule_embeds_directSum_simple k N n hN M halg h_span h_homog
  -- The ambient summand family, indexed by `κ`.
  set Lsum : κ → Type u := fun c => Representation.asModule (L (gκ c)).ρ with hLsum
  haveI : ∀ c, IsSimpleModule (GLAlg k N) (Lsum c) := fun c => hLsimp (gκ c)
  -- Apply the generic isotypic-extraction engine (#4600) to the submodule `M'`.
  obtain ⟨p, h, ⟨eM'⟩⟩ :=
    SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum
      (R := GLAlg k N) Lsum (fun c => hLsimp (gκ c)) e M'
  -- Compose: `M.asModule ≃ M' ≃ ⨁_{j} Lsum (h j) = ⨁_{j} asModule (L (gκ (h j)))`.
  refine ⟨ι, hιFin, hιDec, L, hLsimp, p, fun j => gκ (h j), ⟨?_⟩⟩
  exact eM.trans eM'

end Etingof.PolynomialGLDecomposition

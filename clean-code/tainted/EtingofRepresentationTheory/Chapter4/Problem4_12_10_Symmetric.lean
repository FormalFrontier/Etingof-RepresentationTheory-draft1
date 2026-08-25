import EtingofRepresentationTheory.Chapter4.Problem4_12_10
import EtingofRepresentationTheory.Chapter5.Example5_19_3

/-!
# Problem 4.12.10, symmetric-power form

`Problem4_12_10.lean` proves the **tensor-power** form of Problem 4.12.10: every irreducible
`W` of a finite group `G` occurs inside `V^{⊗n}` for some `n`, whenever `V` is faithful.
The book's *primary* statement is the strictly stronger **symmetric-power** form:

> any irreducible representation of `G` occurs inside `SⁿV` (**and hence** inside `V^{⊗n}`)
> for some `n`.

`SⁿV` is a `G`-direct-summand of `V^{⊗n}` in characteristic `0`, so `W ↪ SⁿV ⟹ W ↪ V^{⊗n}`
but not conversely; the character argument that drives the tensor-power file does not by itself
locate `W` in the symmetric summand.

## This file

* `Etingof.symPowRep ρ n : Representation k G (Sym[k]^n V)` — the **symmetric-power
  representation**, `g ↦ ` the functorial action `symmetricPowerMap (ρ g)` (Example 5.19.3) on
  the `n`-th symmetric power `Sym[k]^n V`. This is the object in which "occurs inside `SⁿV`"
  is phrased.
* `Etingof.symPowEmbedding ρ n` — the `G`-equivariant embedding `Sym[k]^n V ↪ V^{⊗n}`
  intertwining `symPowRep ρ n` with `diagTensorPow ρ n` (characteristic `0`). It realises the
  book's "and hence inside `V^{⊗n}`": composing a nonzero intertwiner `W → SⁿV` with it yields
  a nonzero intertwiner `W → V^{⊗n}`.

The headline symmetric-power occurrence theorem `Etingof.Problem4_12_10_symmetric` is assembled
downstream in `Problem4_12_10_OrbitEval.lean`, once the orbit-evaluation surjection
`⨁ₙ SⁿV ↠ ℂ[G]` (this file's `symPowRep` fed into the book's stabilizer-`1` covector / orbit
interpolation) is available; the Maschke splitting of that surjection places any irreducible `W`
inside some `SⁿV`. The supporting infrastructure — `symPowRep`, `symPowEmbedding`, the covector
lemma `exists_trivialStabilizer_covector`, the regular-embedding pillar
`exists_injective_intertwiner_ofMulAction`, and the summand-extraction pillar
`exists_component_intertwiner_of_ne_zero` — all live here.
-/

open scoped TensorProduct

set_option linter.unusedFintypeInType false

noncomputable section

namespace Etingof

variable {k : Type} [Field k] {G : Type*} [Monoid G]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]

omit [Module.Finite k V] in
/-- `symmetricPowerMap` is functorial in the identity: `Sⁿ(id) = id`. -/
lemma symmetricPowerMap_id {n : ℕ} :
    symmetricPowerMap (n := n) (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) x
  simp only [symmetricPowerMap_mk, PiTensorProduct.map_id, LinearMap.id_coe, id_eq]

omit [Module.Finite k V] in
/-- `symmetricPowerMap` is functorial in composition: `Sⁿ(a ∘ b) = Sⁿ(a) ∘ Sⁿ(b)`. -/
lemma symmetricPowerMap_comp {n : ℕ} (a b : V →ₗ[k] V) :
    symmetricPowerMap (n := n) (a ∘ₗ b) =
      symmetricPowerMap a ∘ₗ symmetricPowerMap b := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := LinearMap.range_eq_top.mp (SymmetricPower.range_mk k (Fin n) V) x
  simp only [symmetricPowerMap_mk, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun
    (PiTensorProduct.map_comp (g := fun _ : Fin n => a) (f := fun _ : Fin n => b)) t

/-- The **symmetric-power representation** `SⁿV` of `G`: from a representation `ρ` on `V`, the
group element `g` acts on `Sym[k]^n V` by the functorial map `symmetricPowerMap (ρ g)`, i.e.
`g · (v₁ ⊙ ⋯ ⊙ vₙ) = (ρ g v₁) ⊙ ⋯ ⊙ (ρ g vₙ)`. -/
def symPowRep (ρ : Representation k G V) (n : ℕ) :
    Representation k G (Sym[k]^n V) where
  toFun g := symmetricPowerMap (ρ g)
  map_one' := by
    simp only [map_one]
    exact symmetricPowerMap_id
  map_mul' g h := by
    simp only [map_mul, Module.End.mul_eq_comp]
    exact symmetricPowerMap_comp _ _

omit [Module.Finite k V] in
@[simp]
theorem symPowRep_apply (ρ : Representation k G V) (n : ℕ) (g : G) :
    symPowRep ρ n g = symmetricPowerMap (ρ g) := rfl

end Etingof

end

section Embedding

open scoped TensorProduct
open Etingof

noncomputable section

variable {k : Type} [Field k] [CharZero k] {G : Type*} [Monoid G]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The `G`-equivariant embedding of the symmetric power into the tensor power,
`Sym[k]^n V ↪ V^{⊗n}`: the composite of the linear isomorphism
`Sym[k]^n V ≃ symInvariants k V n` (symmetric tensors, Example 5.19.3) with the inclusion of the
`Sₙ`-invariant subspace into `V^{⊗n}`. -/
def Etingof.symPowEmbedding (n : ℕ) :
    Sym[k]^n V →ₗ[k] (⨂[k]^n V) :=
  (Etingof.symInvariants k V n).subtype ∘ₗ
    (Etingof.Example5_19_3_symmetricEquiv n).symm.toLinearMap

theorem Etingof.symPowEmbedding_injective (n : ℕ) :
    Function.Injective (Etingof.symPowEmbedding (k := k) (V := V) n) :=
  (Subtype.val_injective).comp (Etingof.Example5_19_3_symmetricEquiv n).symm.injective

/-- The embedding `Sym[k]^n V ↪ V^{⊗n}` intertwines the symmetric-power representation
`symPowRep ρ n` with the diagonal tensor-power representation `diagTensorPow ρ n`: it is a
morphism of `G`-representations. Hence a nonzero intertwiner `W → SⁿV` composes with it to a
nonzero intertwiner `W → V^{⊗n}` — the book's "and hence inside `V^{⊗n}`". -/
theorem Etingof.symPowEmbedding_equivariant (ρ : Representation k G V) (n : ℕ) (g : G) :
    Etingof.symPowEmbedding (k := k) (V := V) n ∘ₗ symPowRep ρ n g =
      diagTensorPow ρ n g ∘ₗ Etingof.symPowEmbedding n := by
  apply LinearMap.ext
  intro y
  set x := (Etingof.Example5_19_3_symmetricEquiv n).symm y with hx
  have hy : y = Etingof.Example5_19_3_symmetricEquiv n x := by
    rw [hx, LinearEquiv.apply_symm_apply]
  simp only [LinearMap.comp_apply, symPowRep_apply, diagTensorPow_apply,
    Etingof.symPowEmbedding, LinearEquiv.coe_coe, Submodule.subtype_apply]
  -- reduce the symmetric side through equivariance of the iso
  rw [hy, LinearEquiv.symm_apply_apply,
    ← Etingof.Example5_19_3_symmetric_equivariant n (ρ g) x,
    LinearEquiv.symm_apply_apply]
  -- both sides are now the diagonal action on the underlying symmetric tensor
  rfl

end

end Embedding

section Covector

open scoped TensorProduct

variable {G : Type*} [Group G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Dual faithfulness: if the dual representation `dual ρ` acts as the identity for `g`, then
`g = 1`. Applying `(dual ρ) g u = u` to functionals shows `ρ g⁻¹` fixes every vector (the dual
separates points over `ℂ`), so `ρ g⁻¹ = ρ 1` and `g = 1` by faithfulness of `ρ`. -/
theorem Etingof.dual_eq_one_imp_eq_one {ρ : Representation ℂ G V} (hρ : Function.Injective ρ)
    {g : G} (hg : (Representation.dual ρ) g = 1) : g = 1 := by
  have hfix : ρ g⁻¹ = ρ (1 : G) := by
    apply LinearMap.ext
    intro v
    rw [map_one, Module.End.one_apply]
    -- `f (ρ g⁻¹ v) = f v` for all functionals `f`, hence `ρ g⁻¹ v = v`.
    have hsub : ∀ f : Module.Dual ℂ V, f (ρ g⁻¹ v - v) = 0 := by
      intro f
      have hf : (Representation.dual ρ) g f = f := by rw [hg]; rfl
      have : f ∘ₗ ρ g⁻¹ = f := hf
      have := LinearMap.congr_fun this v
      simp only [LinearMap.comp_apply, map_sub] at this ⊢
      rw [this, sub_self]
    exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ (ρ g⁻¹ v - v)).mp hsub)
  have : g⁻¹ = 1 := hρ hfix
  rwa [inv_eq_one] at this

/-- **Existence of a trivial-stabilizer covector** (the book's hint for Problem 4.12.10).
For a faithful complex representation `ρ` on a finite-dimensional `V`, there is a covector
`u ∈ V*` whose stabilizer in `G` under the dual representation is trivial: `(dual ρ) g u = u`
forces `g = 1`.

The covectors fixed by some `g ≠ 1` form a finite union of *proper* subspaces of `V*`
(proper because `(dual ρ) g ≠ 1`, by `Etingof.dual_eq_one_imp_eq_one`). A vector space over the
infinite field `ℂ` is not a finite union of proper subspaces
(`Subspace.exists_eq_top_of_iUnion_eq_univ`), so some `u` avoids them all. -/
theorem Etingof.exists_trivialStabilizer_covector [Finite G]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ) :
    ∃ u : Module.Dual ℂ V, ∀ g : G, (Representation.dual ρ) g u = u → g = 1 := by
  classical
  -- The fixed subspace of a nonidentity `g`.
  set Fix : {g : G // g ≠ 1} → Submodule ℂ (Module.Dual ℂ V) :=
    fun g => LinearMap.ker ((Representation.dual ρ) g.1 - 1) with hFix
  -- Each `Fix g` is proper: `Fix g = ⊤` would make `(dual ρ) g = 1`, contradicting `g ≠ 1`.
  have hproper : ∀ g, Fix g ≠ ⊤ := by
    intro g hg
    rw [hFix, LinearMap.ker_eq_top, sub_eq_zero] at hg
    exact g.2 (Etingof.dual_eq_one_imp_eq_one hρ hg)
  -- Hence the union of the `Fix g` does not cover `V*`.
  have hcover : ⋃ g, (Fix g : Set (Module.Dual ℂ V)) ≠ Set.univ := by
    intro huniv
    obtain ⟨g, hg⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ huniv
    exact hproper g hg
  -- Pick `u` outside every `Fix g`.
  obtain ⟨u, hu⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hcover
  refine ⟨u, fun g hgu => ?_⟩
  by_contra hg1
  refine hu (Set.mem_iUnion.mpr ⟨⟨g, hg1⟩, ?_⟩)
  simp only [hFix, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]
  exact hgu

end Covector

section DirectSumExtract

open scoped DirectSum

variable {k G : Type*} [CommSemiring k] [Monoid G]
  {ι : Type*} {V : ι → Type*}
  [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]
  {W : Type*} [AddCommMonoid W] [Module k W]

/-- The projection `DirectSum.component` onto the `i`-th summand intertwines the direct-sum
representation `Representation.directSum ρs` with the component representation `ρs i`. -/
theorem Representation.directSum_component_equivariant
    (ρs : (i : ι) → Representation k G (V i)) (i : ι) (g : G) :
    DirectSum.component k ι V i ∘ₗ (Representation.directSum ρs) g =
      ρs i g ∘ₗ DirectSum.component k ι V i := by
  ext y
  simp only [LinearMap.comp_apply, Representation.directSum_apply,
    ← DirectSum.apply_eq_component, DirectSum.lmap_apply]

/-- **Single-summand extraction.** A nonzero `G`-equivariant map `φ : W → ⨁ i, V i` into a
direct sum of representations yields, for some index `i`, a nonzero `G`-equivariant map
`W → V i`: postcompose `φ` with the (equivariant) projection onto a summand on which `φ` does
not vanish. This turns `Hom_G(W, ⊕ᵢ Vᵢ) ≠ 0` into `Hom_G(W, Vᵢ) ≠ 0` for a single `i`. -/
theorem exists_component_intertwiner_of_ne_zero
    (ρs : (i : ι) → Representation k G (V i)) (σ : Representation k G W)
    (φ : W →ₗ[k] (⨁ i, V i)) (hφ : φ ≠ 0)
    (hφ_int : ∀ g, φ ∘ₗ σ g = (Representation.directSum ρs) g ∘ₗ φ) :
    ∃ (i : ι) (ψ : W →ₗ[k] V i), ψ ≠ 0 ∧ ∀ g, ψ ∘ₗ σ g = ρs i g ∘ₗ ψ := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hφ
  have hcomp : ∃ i, DirectSum.component k ι V i (φ w) ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hw (DirectSum.ext_component k fun i => by simp [h i])
  obtain ⟨i, hi⟩ := hcomp
  refine ⟨i, DirectSum.component k ι V i ∘ₗ φ, ?_, fun g => ?_⟩
  · exact fun hzero => hi (by simpa using LinearMap.congr_fun hzero w)
  · rw [LinearMap.comp_assoc, hφ_int g, ← LinearMap.comp_assoc,
      Representation.directSum_component_equivariant, LinearMap.comp_assoc]

end DirectSumExtract

section AsModuleHom

open scoped MonoidAlgebra

namespace Representation

variable {k G V W : Type*} [CommSemiring k] [Monoid G]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- The `k`-linear intertwiner underlying a `MonoidAlgebra k G`-linear map of `asModule`s: the
reverse of `asModuleHomOfIntertwiner`. Its `G`-equivariance is
`intertwinerOfAsModuleHom_equivariant`. -/
noncomputable def intertwinerOfAsModuleHom
    (h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule) : V →ₗ[k] W :=
  σ.asModuleEquiv.toLinearMap ∘ₗ h.restrictScalars k ∘ₗ ρ.asModuleEquiv.symm.toLinearMap

@[simp] theorem intertwinerOfAsModuleHom_apply
    (h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule) (x : V) :
    intertwinerOfAsModuleHom h x = σ.asModuleEquiv (h (ρ.asModuleEquiv.symm x)) := rfl

theorem intertwinerOfAsModuleHom_equivariant
    (h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule) (g : G) (x : V) :
    intertwinerOfAsModuleHom h (ρ g x) = σ g (intertwinerOfAsModuleHom h x) := by
  have key : h (MonoidAlgebra.single g (1 : k) • ρ.asModuleEquiv.symm x)
      = MonoidAlgebra.single g (1 : k) • h (ρ.asModuleEquiv.symm x) := map_smul h _ _
  rw [Representation.single_smul, Representation.single_smul, one_smul, one_smul] at key
  exact key

theorem intertwinerOfAsModuleHom_injective
    {h : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule} (hh : Function.Injective h) :
    Function.Injective (intertwinerOfAsModuleHom h) := by
  intro a b hab
  simp only [intertwinerOfAsModuleHom_apply] at hab
  exact ρ.asModuleEquiv.symm.injective (hh (σ.asModuleEquiv.injective hab))

end Representation

end AsModuleHom

section SimpleEmbedsRegular

open scoped MonoidAlgebra
open Representation

/-- **A simple representation embeds in the regular representation.** For a finite group `G` over
a field `k` with `Nat.card G ≠ 0` in `k` (e.g. characteristic `0`), any representation `σ` whose
`asModule` is a simple `k[G]`-module admits an injective `G`-equivariant linear map into the
regular representation `Representation.ofMulAction k G G` on `k[G]`.

The simple module `σ.asModule` is a quotient `k[G] ⧸ I` (`isSimpleModule_iff_quot_maximal`), giving
a `k[G]`-linear surjection from the (semisimple, by Maschke) regular module onto it; the surjection
splits (`IsSemisimpleModule.lifting_property`), and the section — an injective `k[G]`-module hom —
is repackaged as an intertwiner by `Representation.intertwinerOfAsModuleHom`. -/
theorem exists_injective_intertwiner_ofMulAction
    {k G : Type*} [Field k] [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G W)
    (hσ : IsSimpleModule (MonoidAlgebra k G) σ.asModule) :
    ∃ φ : W →ₗ[k] MonoidAlgebra k G, Function.Injective φ ∧
      ∀ g : G, φ ∘ₗ σ g = (Representation.ofMulAction k G G) g ∘ₗ φ := by
  classical
  obtain ⟨I, _hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hσ
  set reg := Representation.ofMulActionSelfAsModuleEquiv (k := k) (G := G) with hreg
  -- The regular module surjects onto the simple `σ.asModule` via `k[G] ↠ k[G]⧸I ≃ σ.asModule`.
  let f : (Representation.ofMulAction k G G).asModule →ₗ[MonoidAlgebra k G] σ.asModule :=
    e.symm.toLinearMap ∘ₗ I.mkQ ∘ₗ reg.toLinearMap
  have hf : Function.Surjective f :=
    e.symm.surjective.comp ((Submodule.mkQ_surjective I).comp reg.surjective)
  -- Maschke: the regular module is semisimple, so the surjection splits.
  obtain ⟨h, hfh⟩ := IsSemisimpleModule.lifting_property (R := MonoidAlgebra k G)
    (M := (Representation.ofMulAction k G G).asModule) (N := σ.asModule)
    (P := σ.asModule) f hf (LinearMap.id)
  have hlinv : Function.LeftInverse f h := fun x => by
    simpa using LinearMap.congr_fun hfh x
  refine ⟨Representation.intertwinerOfAsModuleHom h,
    Representation.intertwinerOfAsModuleHom_injective hlinv.injective, fun g => ?_⟩
  exact LinearMap.ext fun x => Representation.intertwinerOfAsModuleHom_equivariant h g x

end SimpleEmbedsRegular

/-
The headline occurrence theorem `Etingof.Problem4_12_10_symmetric` is assembled in
`Problem4_12_10_OrbitEval.lean`, which imports this file for `symPowRep` and the two Maschke
pillars (`exists_injective_intertwiner_ofMulAction`, `exists_component_intertwiner_of_ne_zero`)
and additionally supplies the orbit-evaluation surjection `⨁ₙ SⁿV ↠ ℂ[G]` that the assembly
splits. The theorem cannot live here because that surjection depends on this file.
-/

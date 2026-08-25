import EtingofRepresentationTheory.Chapter8.TensorOverModule
import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import Mathlib.Algebra.Category.ModuleCat.Abelian

set_option backward.isDefEq.respectTransparency false

/-!
# The `k`-linear tensor-right functor `M ↦ M ⊗_A N`

`Etingof.tensorRightFunctor A N : ModuleCat Aᵐᵒᵖ ⥤ AddCommGrpCat` (`Definition8_2_3.lean`) sends a
right `A`-module `M` to the ring-tensor `M ⊗_A N`, as an abelian group. For the Künneth / four-fold
rearrangement work on `Tor` over a tensor product of algebras (Problem 8.2.8, milestone (c)) we need
the same construction landing in `ModuleCat k`: the milestone-(c) rearrangement iso is stated
against `HomologicalComplex.tensorObj` over `ModuleCat.{u} k` (the shape consumed by the Künneth
machinery `Chapter7/KunnethChainComplexNat.lean`), so the two factors `P•ᵢ ⊗_{Aᵢ} Nᵢ` and the total
complex `(P•₁ ⊗_k P•₂) ⊗_{A₁⊗A₂} (N₁ ⊗_k N₂)` must all be `ChainComplex (ModuleCat.{u} k) ℕ`.

This file provides that `k`-linear upgrade:

* `Etingof.tensorRightMapₖ A N f : tensorOver A N M →ₗ[k] tensorOver A N M'`: the `k`-linear
  form of `tensorRightMap A N f`, for an `Aᵐᵒᵖ`-linear `f`; its underlying additive map is
  `tensorRightMap A N f`.
* `Etingof.tensorRightFunctorₖ k A N : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} k`, `M ↦ M ⊗_A N`.
* `Etingof.tensorRightFunctorₖ_forget₂` : the natural iso
  `tensorRightFunctorₖ k A N ⋙ forget₂ (ModuleCat k) AddCommGrpCat ≅ tensorRightFunctor A N`, which
  lets a `ModuleCat k`-complex iso descend to the `AddCommGrpCat` homology defining `Tor`.
* `Additive (tensorRightFunctorₖ k A N)`.

The per-object `k`-module structure on `M : ModuleCat Aᵐᵒᵖ` is the restriction of scalars along
`algebraMap k Aᵐᵒᵖ` (`Module.compHom`), the same idiom as `Chapter8/ExternalTensorComplex.lean`; the
`k`-module structure on `tensorOver A N M` is then the one from `Chapter8/TensorOverModule.lean`.
-/

open CategoryTheory TensorProduct

namespace Etingof

universe u

variable (k : Type u) [CommRing k]
variable (A : Type u) [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module A N]

/-- Restriction of scalars `k → Aᵐᵒᵖ` on each right `A`-module, matching the local instances of
`Chapter8/ExternalTensorComplex.lean`. -/
noncomputable local instance instModuleKObj (M : ModuleCat.{u} Aᵐᵒᵖ) : Module k M :=
  Module.compHom M (algebraMap k Aᵐᵒᵖ)

local instance instTowerObj (M : ModuleCat.{u} Aᵐᵒᵖ) : IsScalarTower k Aᵐᵒᵖ M :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance instCommObj (M : ModuleCat.{u} Aᵐᵒᵖ) : SMulCommClass k Aᵐᵒᵖ M where
  smul_comm c a m := by
    change (algebraMap k Aᵐᵒᵖ c) • (a • m) = a • ((algebraMap k Aᵐᵒᵖ c) • m)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The additive map `tensorRightMap A N f` on a simple-tensor class. -/
theorem tensorRightMap_mk {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') (m : M) (n : N) :
    tensorRightMap A N f (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n) : tensorOver A N M)
      = (QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) : tensorOver A N M') := rfl

/-- `tensorRightMap A N f` is `k`-linear: `k` acts through `Aᵐᵒᵖ` on `M, M'` (so `f` is `k`-linear)
and the `k`-action lands on the left tensor factor. -/
theorem tensorRightMap_smul {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') (c : k)
    (z : tensorOver A N M) :
    tensorRightMap A N f (c • z) = c • tensorRightMap A N f z := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  induction y with
  | zero => simp
  | tmul m n =>
      have hf : f.hom (c • m) = c • f.hom m := map_smul f.hom (algebraMap k Aᵐᵒᵖ c) m
      rw [smul_mk, TensorProduct.smul_tmul', tensorRightMap_mk, tensorRightMap_mk, hf, smul_mk,
        TensorProduct.smul_tmul']
  | add a b ha hb =>
      rw [QuotientAddGroup.mk_add, smul_add, map_add, map_add, ha, hb, smul_add]

/-- The `k`-linear map `M ⊗_A N → M' ⊗_A N` induced by a right `A`-module map `f : M ⟶ M'`. Its
underlying additive map is `tensorRightMap A N f`. -/
noncomputable def tensorRightMapₖ {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    tensorOver A N M →ₗ[k] tensorOver A N M' where
  toFun := tensorRightMap A N f
  map_add' := (tensorRightMap A N f).map_add
  map_smul' c z := tensorRightMap_smul k A N f c z

@[simp] theorem tensorRightMapₖ_mk {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') (m : M) (n : N) :
    tensorRightMapₖ k A N f (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n) : tensorOver A N M)
      = (QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) : tensorOver A N M') := rfl

/-- The `k`-linear functor `M ↦ M ⊗_A N` from right `A`-modules to `k`-vector spaces. This is the
`ModuleCat k`-valued form of `Etingof.tensorRightFunctor A N`. -/
noncomputable def tensorRightFunctorₖ : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (tensorOver A N M)
  map {M M'} f := ModuleCat.ofHom (tensorRightMapₖ k A N f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => rw [QuotientAddGroup.mk_add, map_add, map_add, ha, hb]
  map_comp {M M' M''} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => rw [QuotientAddGroup.mk_add, map_add, map_add, ha, hb]

@[simp] theorem tensorRightFunctorₖ_map_mk {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    (m : M) (n : N) :
    (tensorRightFunctorₖ k A N).map f
        (QuotientAddGroup.mk (m ⊗ₜ[ℤ] n) : tensorOver A N M)
      = (QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) : tensorOver A N M') := rfl

/-- `tensorRightFunctorₖ` is additive, so it can be applied to homological complexes and preserves
the degreewise finite biproducts. -/
instance : (tensorRightFunctorₖ k A N).Additive where
  map_add {M M' f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_add, LinearMap.add_apply]
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n =>
        change (QuotientAddGroup.mk ((f + g).hom m ⊗ₜ[ℤ] n) : tensorOver A N M')
          = QuotientAddGroup.mk (f.hom m ⊗ₜ[ℤ] n) + QuotientAddGroup.mk (g.hom m ⊗ₜ[ℤ] n)
        rw [← QuotientAddGroup.mk_add, ModuleCat.hom_add, LinearMap.add_apply, add_tmul]
    | add a b ha hb =>
        rw [QuotientAddGroup.mk_add, map_add, map_add, map_add, ha, hb]
        abel

/-- The `k`-linear functor `tensorRightFunctorₖ`, followed by the forgetful functor to abelian
groups, is the original `AddCommGrpCat`-valued `tensorRightFunctor`. This lets a `ModuleCat k`-level
complex isomorphism descend to the `AddCommGrpCat` homology that defines `Tor`. -/
noncomputable def tensorRightFunctorₖ_forget₂ :
    tensorRightFunctorₖ k A N ⋙ forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
      ≅ tensorRightFunctor A N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M M' f
    simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

/-- The `k`-linear `n`-th `Tor` functor `Torₙᴬ(-, N) : (right A-modules) ⥤ ModuleCat k`, the `n`-th
left derived functor of the `k`-linear `- ⊗_A N`. It refines `Etingof.TorFunctor A N n` (whose
values are the underlying abelian groups, via `tensorRightFunctorₖ_forget₂`). -/
noncomputable def TorFunctorₖ (n : ℕ) : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  Functor.leftDerived (tensorRightFunctorₖ k A N) n

/-- `Torₙᴬ(M, N)` as a `k`-vector space: the `n`-th left derived functor of the `k`-linear
`- ⊗_A N` evaluated at the right `A`-module `M`. Its underlying abelian group is `Etingof.Tor A N M
n` (via `tensorRightFunctorₖ_forget₂`), so this is the `k`-linear refinement of `Tor` used by the
Künneth formula of Problem 8.2.8, which tensors the factor `Tor`s over the field `k`. -/
noncomputable def Torₖ (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) : ModuleCat.{u} k :=
  (TorFunctorₖ k A N n).obj M

/-- **`Torₖ` from a chosen projective resolution.** For any projective resolution `P•` of the right
`A`-module `M`, `Torₙᴬ(M, N)` (as a `k`-vector space) is canonically isomorphic to the `n`-th
homology of the `k`-linear complex `P• ⊗_A N`. The `k`-linear analogue of
`Etingof.torIsoHomologyTensorRight`, obtained from `ProjectiveResolution.isoLeftDerivedObj`. -/
noncomputable def torIsoHomologyTensorRightₖ (M : ModuleCat.{u} Aᵐᵒᵖ)
    (P : ProjectiveResolution M) (n : ℕ) :
    Torₖ k A N M n ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n).obj
        (((tensorRightFunctorₖ k A N).mapHomologicalComplex _).obj P.complex) :=
  P.isoLeftDerivedObj (tensorRightFunctorₖ k A N) n

end Etingof

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Problem 3.9.1: Extensions of representations and `Ext¹`

Let `A` be an algebra and `V, W` representations of `A`. This problem classifies the
representations `U` of `A` such that `V` is a subrepresentation of `U` and `U / V = W`.
Identifying `U` with `V ⊕ W` as a vector space, the operator `ρ_U(a)` has block-triangular
form
`ρ_U(a) = [[ρ_V(a), f(a)], [0, ρ_W(a)]]`,
for a linear map `f : A → Homₖ(W, V)`.

We model a representation of `A` as an `A`-module that is also a `k`-module with
`IsScalarTower k A V`; the action of `a` is `ρ_V(a) = Algebra.lsmul k k V a : V →ₗ[k] V`.
The block operator `ρ_U(a)` is `blockOp f a : V × W →ₗ[k] V × W`.

* **(a)** `ρ_U` is a representation (i.e. multiplicative in `a`) iff `f` is a **1-cocycle**:
  `f(ab) = ρ_V(a) ∘ f(b) + f(a) ∘ ρ_W(b)`. Cocycles form the subspace
  `Z¹(W, V) = cocycles`.
* **(b)** For `X : W →ₗ[k] V`, the **coboundary** `dX(a) = ρ_V(a) ∘ X − X ∘ ρ_W(a)`
  (`coboundaryOf X`) is a cocycle, and vanishes iff `X` is a homomorphism of
  representations (`A`-linear). Coboundaries form the subspace
  `B¹(W, V) = coboundaries ⊆ Z¹`, and `Ext¹(W, V) = Z¹ / B¹` is `Ext1`.
* **(c)**, **(d)**: isomorphism classification of the extensions; see the deferred
  statements at the end of the file.

Statement pass: definitions are constructed; the proofs are left as `sorry`.
-/

namespace Etingof.Problem3_9_1

variable (k : Type*) (A : Type*) (V : Type*) (W : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

/-- The action `ρ_V(a) : V →ₗ[k] V`, `v ↦ a • v`, of an algebra element on a
representation. -/
noncomputable abbrev rho (M : Type*) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] (a : A) : M →ₗ[k] M :=
  Algebra.lsmul k k M a

/-- **1-cocycle condition** (Problem 3.9.1(a)). A linear map `f : A →ₗ[k] (W →ₗ[k] V)` is a
1-cocycle if `f(ab) = ρ_V(a) ∘ f(b) + f(a) ∘ ρ_W(b)` for all `a, b`. -/
def IsCocycle (f : A →ₗ[k] (W →ₗ[k] V)) : Prop :=
  ∀ a b : A, f (a * b) = (rho k A V a).comp (f b) + (f a).comp (rho k A W b)

/-- The block-triangular operator `ρ_U(a) = [[ρ_V(a), f(a)], [0, ρ_W(a)]]` acting on
`V × W`: `(v, w) ↦ (ρ_V(a) v + f(a) w, ρ_W(a) w)`. -/
noncomputable def blockOp (f : A →ₗ[k] (W →ₗ[k] V)) (a : A) : (V × W) →ₗ[k] (V × W) :=
  LinearMap.prod
    (LinearMap.coprod (rho k A V a) (f a))
    ((rho k A W a).comp (LinearMap.snd k V W))

/-- Applying the block operator to a pair: `blockOp f a (v, w) = (a • v + f a w, a • w)`. -/
theorem blockOp_apply (f : A →ₗ[k] (W →ₗ[k] V)) (a : A) (v : V) (w : W) :
    blockOp k A V W f a (v, w) = (a • v + f a w, a • w) := by
  simp [blockOp, Algebra.lsmul_coe]

/-- **Problem 3.9.1(a).** The block-triangular assignment `a ↦ blockOp f a` is multiplicative
(hence a representation on `V × W`) if and only if `f` is a 1-cocycle. -/
theorem blockOp_mul_iff_isCocycle (f : A →ₗ[k] (W →ₗ[k] V)) :
    (∀ a b : A, blockOp k A V W f (a * b)
        = (blockOp k A V W f a).comp (blockOp k A V W f b))
      ↔ IsCocycle k A V W f := by
  constructor
  · intro h a b
    ext w
    have h2 := LinearMap.congr_fun (h a b) (0, w)
    rw [LinearMap.comp_apply, blockOp_apply, blockOp_apply, blockOp_apply] at h2
    simp only [smul_zero, zero_add, Prod.mk.injEq] at h2
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe]
    exact h2.1
  · intro h a b
    apply LinearMap.ext
    rintro ⟨v, w⟩
    have hc := LinearMap.congr_fun (h a b) w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
    rw [LinearMap.comp_apply, blockOp_apply, blockOp_apply, blockOp_apply, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hc]; simp only [mul_smul, smul_add]; abel
    · rw [mul_smul]

/-- The space `Z¹(W, V)` of 1-cocycles, a `k`-subspace of `A →ₗ[k] (W →ₗ[k] V)`. -/
def cocycles : Submodule k (A →ₗ[k] (W →ₗ[k] V)) where
  carrier := {f | IsCocycle k A V W f}
  add_mem' {f g} hf hg := by
    intro a b
    simp only [LinearMap.add_apply, hf a b, hg a b, LinearMap.comp_add, LinearMap.add_comp]
    abel
  zero_mem' := by intro a b; simp
  smul_mem' c f hf := by
    intro a b
    simp only [LinearMap.smul_apply, hf a b, LinearMap.comp_smul, LinearMap.smul_comp, smul_add]

/-- The **coboundary** `dX` of a linear map `X : W →ₗ[k] V`:
`dX(a) = ρ_V(a) ∘ X − X ∘ ρ_W(a)`, an element of `A →ₗ[k] (W →ₗ[k] V)`. Built from linear
combinators, so linear in `a` automatically. -/
noncomputable def coboundaryOf (X : W →ₗ[k] V) : A →ₗ[k] (W →ₗ[k] V) :=
  ((LinearMap.llcomp k W V V).flip X).comp (Algebra.lsmul k k V).toLinearMap
    - (LinearMap.llcomp k W W V X).comp (Algebra.lsmul k k W).toLinearMap

/-- **Problem 3.9.1(b), first part.** Every coboundary `dX` is a 1-cocycle. -/
theorem coboundaryOf_isCocycle (X : W →ₗ[k] V) : IsCocycle k A V W (coboundaryOf k A V W X) := by
  intro a b
  ext w
  simp only [coboundaryOf, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.llcomp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe,
    mul_smul, map_sub]
  abel

/-- **Problem 3.9.1(b), second part.** The coboundary `dX` vanishes if and only if `X` is a
homomorphism of representations, i.e. `A`-linear. -/
theorem coboundaryOf_eq_zero_iff (X : W →ₗ[k] V) :
    coboundaryOf k A V W X = 0 ↔ ∀ (a : A) (w : W), X (a • w) = a • X w := by
  constructor
  · intro h a w
    have := LinearMap.congr_fun (LinearMap.congr_fun h a) w
    simp only [coboundaryOf, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
      LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe, LinearMap.zero_apply,
      sub_eq_zero] at this
    exact this.symm
  · intro h
    ext a w
    simp only [coboundaryOf, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
      LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe, LinearMap.zero_apply,
      sub_eq_zero, h a w]

/-- The space `B¹(W, V)` of coboundaries: the image of the coboundary map
`X ↦ dX`. As the image of a linear map it is a `k`-subspace, here presented as the span of
the range. -/
def coboundaries : Submodule k (A →ₗ[k] (W →ₗ[k] V)) :=
  Submodule.span k (Set.range (coboundaryOf k A V W))

/-- **Problem 3.9.1(b).** Coboundaries are cocycles: `B¹ ⊆ Z¹`. -/
theorem coboundaries_le_cocycles :
    coboundaries k A V W ≤ cocycles k A V W := by
  rw [coboundaries, Submodule.span_le, Set.range_subset_iff]
  intro X
  exact coboundaryOf_isCocycle k A V W X

/-- `Ext¹(W, V) = Z¹ / B¹`, the quotient of cocycles by coboundaries. -/
abbrev Ext1 : Type _ :=
  (cocycles k A V W) ⧸ (coboundaries k A V W).submoduleOf (cocycles k A V W)

/-! ## Parts (c) and (d)

Rather than constructing the extension module `U_f` explicitly, we phrase isomorphism of
extensions via `k`-linear intertwiners of the block operators of the special triangular
form `[[1, ∗], [0, 1]]`. -/

/-- An isomorphism `U_f ≅ U_{f'}` of extensions (as representations) is a `k`-linear
automorphism `φ` of `V × W` intertwining the block operators: `φ ∘ ρ_{U_f}(a) = ρ_{U_{f'}}(a)
∘ φ` for all `a`. -/
def IntertwinesExt (f f' : A →ₗ[k] (W →ₗ[k] V)) (φ : (V × W) ≃ₗ[k] (V × W)) : Prop :=
  ∀ a : A, (φ.toLinearMap).comp (blockOp k A V W f a)
    = (blockOp k A V W f' a).comp φ.toLinearMap

/-- **Problem 3.9.1(c).** If `f − f'` is a coboundary, then the corresponding extensions are
isomorphic representations. -/
theorem iso_of_sub_mem_coboundaries (f f' : A →ₗ[k] (W →ₗ[k] V))
    (hf : IsCocycle k A V W f) (hf' : IsCocycle k A V W f')
    (hsub : f - f' ∈ coboundaries k A V W) :
    ∃ φ : (V × W) ≃ₗ[k] (V × W), IntertwinesExt k A V W f f' φ := by
  sorry

/-- **Problem 3.9.1(d).** For finite dimensional irreducible `V` and `W`, the extensions
`U_f` and `U_{f'}` are isomorphic if and only if the cocycles `f` and `f'` are proportional
modulo coboundaries (their classes in `Ext¹` are proportional). -/
theorem irreducible_ext_iso_iff_proportional
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule A W]
    (f f' : A →ₗ[k] (W →ₗ[k] V)) (hf : IsCocycle k A V W f) (hf' : IsCocycle k A V W f') :
    (∃ φ : (V × W) ≃ₗ[k] (V × W), IntertwinesExt k A V W f f' φ)
      ↔ ∃ c : k, f - c • f' ∈ coboundaries k A V W := by
  sorry

end Etingof.Problem3_9_1

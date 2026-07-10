import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import EtingofRepresentationTheory.Chapter2.Corollary2_3_10

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
* **(c)**, **(d)**: isomorphism classification of the extensions; see the statements at the
  end of the file. Part (d) requires `IsAlgClosed k` and is phrased as a nonzero-ratio
  proportionality (`∃ c ≠ 0, f − c • f' ∈ B¹`), the faithful form of the book's
  `ℙ Ext¹(W, V)` classification.

All parts are proved (`sorry`-free).
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

/-- Pointwise formula for a coboundary: `dX(a)(w) = a • X w - X (a • w)`. -/
theorem coboundaryOf_apply (X : W →ₗ[k] V) (a : A) (w : W) :
    coboundaryOf k A V W X a w = a • X w - X (a • w) := by
  simp only [coboundaryOf, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
    LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe]

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

/-- The coboundary map `X ↦ dX` bundled as a `k`-linear map. Its range is `coboundaries`. -/
noncomputable def coboundaryLinear : (W →ₗ[k] V) →ₗ[k] (A →ₗ[k] (W →ₗ[k] V)) where
  toFun := coboundaryOf k A V W
  map_add' X Y := by
    ext a w
    simp only [coboundaryOf_apply, LinearMap.add_apply, smul_add]
    abel
  map_smul' c X := by
    ext a w
    simp only [coboundaryOf_apply, LinearMap.smul_apply, RingHom.id_apply, smul_sub,
      smul_comm a c]

@[simp] theorem coboundaryLinear_apply (X : W →ₗ[k] V) :
    coboundaryLinear k A V W X = coboundaryOf k A V W X := rfl

/-- `coboundaries` is exactly the range of the coboundary map. -/
theorem coboundaries_eq_range :
    coboundaries k A V W = LinearMap.range (coboundaryLinear k A V W) := by
  apply le_antisymm
  · rw [coboundaries, Submodule.span_le]
    rintro _ ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  · rintro _ ⟨X, rfl⟩
    exact Submodule.subset_span ⟨X, rfl⟩

/-- Membership in `coboundaries` means being a coboundary `dX` for some `X`. -/
theorem mem_coboundaries_iff (g : A →ₗ[k] (W →ₗ[k] V)) :
    g ∈ coboundaries k A V W ↔ ∃ X : W →ₗ[k] V, coboundaryOf k A V W X = g := by
  rw [coboundaries_eq_range, LinearMap.mem_range]
  simp only [coboundaryLinear_apply]

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
  obtain ⟨X, hX⟩ := (mem_coboundaries_iff k A V W (f - f')).1 hsub
  -- `φ = [[1, X], [0, 1]]`, i.e. `(v, w) ↦ (v + X w, w)`, with inverse `(v, w) ↦ (v - X w, w)`.
  set L : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W + X ∘ₗ LinearMap.snd k V W) (LinearMap.snd k V W)
    with hL
  set Linv : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W - X ∘ₗ LinearMap.snd k V W) (LinearMap.snd k V W)
    with hLinv
  have Lapp : ∀ p : V × W, L p = (p.1 + X p.2, p.2) := fun p => by
    simp [hL, Function.prod_apply]
  have Linvapp : ∀ p : V × W, Linv p = (p.1 - X p.2, p.2) := fun p => by
    simp [hLinv, Function.prod_apply]
  refine ⟨LinearEquiv.ofLinear L Linv ?_ ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp [Lapp, Linvapp]
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp [Lapp, Linvapp]
  intro a
  apply LinearMap.ext
  rintro ⟨v, w⟩
  -- The off-diagonal identity: `(f - f') a w = a • X w - X (a • w)`.
  have key : a • X w + f' a w = f a w + X (a • w) := by
    have h := LinearMap.congr_fun (LinearMap.congr_fun hX a) w
    rw [coboundaryOf_apply, LinearMap.sub_apply] at h
    exact sub_eq_sub_iff_add_eq_add.1 h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, blockOp_apply,
    Lapp, smul_add]
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  simp only [add_assoc, ← key]

/-- The "proportional ⇒ isomorphic" direction of Problem 3.9.1(d), in the nondegenerate case
`c ≠ 0`. If `f − c • f'` is a coboundary for some nonzero scalar `c`, then the extensions
`U_f` and `U_{f'}` are isomorphic representations, via the block map `φ = [[1, X], [0, c]]`.

This holds over any field (no irreducibility or finite dimensionality needed) and is the
reusable half of part (d). The degenerate case `c = 0` reduces to `f` being a coboundary,
which makes `U_f` split but says nothing about `U_{f'}`; it does *not* give
`U_f ≅ U_{f'}` in general. -/
theorem ext_iso_of_sub_smul_mem_coboundaries (f f' : A →ₗ[k] (W →ₗ[k] V))
    (c : k) (hc : c ≠ 0) (hsub : f - c • f' ∈ coboundaries k A V W) :
    ∃ φ : (V × W) ≃ₗ[k] (V × W), IntertwinesExt k A V W f f' φ := by
  obtain ⟨X, hX⟩ := (mem_coboundaries_iff k A V W (f - c • f')).1 hsub
  -- `φ = [[1, X], [0, c]]`, i.e. `(v, w) ↦ (v + X w, c • w)`.
  set L : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W + X ∘ₗ LinearMap.snd k V W) (c • LinearMap.snd k V W)
    with hL
  set Linv : (V × W) →ₗ[k] (V × W) :=
    LinearMap.prod (LinearMap.fst k V W - c⁻¹ • (X ∘ₗ LinearMap.snd k V W))
      (c⁻¹ • LinearMap.snd k V W) with hLinv
  have Lapp : ∀ p : V × W, L p = (p.1 + X p.2, c • p.2) := fun p => by
    simp [hL, Function.prod_apply]
  have Linvapp : ∀ p : V × W, Linv p = (p.1 - c⁻¹ • X p.2, c⁻¹ • p.2) := fun p => by
    simp [hLinv, Function.prod_apply]
  refine ⟨LinearEquiv.ofLinear L Linv ?_ ?_, ?_⟩
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, Lapp, Linvapp, LinearMap.id_coe, id_eq, map_smul,
      smul_inv_smul₀ hc, sub_add_cancel]
  · apply LinearMap.ext
    rintro ⟨v, w⟩
    simp only [LinearMap.comp_apply, Lapp, Linvapp, LinearMap.id_coe, id_eq, map_smul,
      inv_smul_smul₀ hc, add_sub_cancel_right]
  intro a
  apply LinearMap.ext
  rintro ⟨v, w⟩
  -- Off-diagonal identity: `(f - c • f') a w = a • X w - X (a • w)`.
  have key : a • X w + c • f' a w = f a w + X (a • w) := by
    have h := LinearMap.congr_fun (LinearMap.congr_fun hX a) w
    simp only [coboundaryOf_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h
    exact sub_eq_sub_iff_add_eq_add.1 h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, blockOp_apply,
    Lapp, smul_add, map_smul]
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [add_assoc, ← key]
  · rw [smul_comm]

/-- **Problem 3.9.1(d).** Over an algebraically closed field, for finite dimensional irreducible
`V` and `W`, the extensions `U_f` and `U_{f'}` are isomorphic representations if and only if the
cocycle classes `[f]` and `[f']` are proportional with a **nonzero** ratio: there is `c ≠ 0` with
`f − c • f' ∈ B¹`.

This is the faithful form of the book's part (d): the trivial class (`f ∈ B¹`, i.e. `U_f` splits)
together with the projective space `ℙ Ext¹(W, V)` of lines of nonzero classes exhaust the
isomorphism classes of extensions of `W` by `V`. The `c ≠ 0` constraint is essential — a spurious
`c = 0` would only assert `f ∈ B¹`, which says nothing about `f'` and would make the naive `iff`
false. Algebraic closedness enters through Schur's lemma (`Etingof.Corollary_2_3_10`): over a
non-closed field `End_A V` is a division ring strictly larger than `k`, and the iso classes are
`Ext¹` modulo the `D_V^× × D_W^×` action rather than `ℙ_k Ext¹`.

The proof of `⇐` is the reusable helper `ext_iso_of_sub_smul_mem_coboundaries`. For `⇒`, block
decompose the intertwiner `φ = [[α, β], [γ, δ]]`. The lower-left block `γ : V → W` is `A`-linear,
so by Schur it is either `0` or an isomorphism. If `γ = 0`, then `α`, `δ` are `A`-linear scalars
`s, t` (Schur over an algebraically closed field, both nonzero since `φ` is invertible), and the
`(1,2)` block identity gives `s • f − t • f' = dβ`, so `f − (t/s) • f' ∈ B¹` with `t/s ≠ 0`. If
`γ` is an isomorphism (only possible when `V ≅ W`), the `(1,1)` and `(2,2)` blocks force both `f`
and `f'` to be coboundaries, so `f − 1 • f' ∈ B¹`. -/
theorem irreducible_ext_iso_iff_proportional [IsAlgClosed k]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule A W]
    (f f' : A →ₗ[k] (W →ₗ[k] V)) (_hf : IsCocycle k A V W f) (_hf' : IsCocycle k A V W f') :
    (∃ φ : (V × W) ≃ₗ[k] (V × W), IntertwinesExt k A V W f f' φ)
      ↔ ∃ c : k, c ≠ 0 ∧ f - c • f' ∈ coboundaries k A V W := by
  constructor
  · rintro ⟨φ, hφ⟩
    -- Block components of `φ` in the `V × W` basis.
    set P : (V × W) →ₗ[k] V := (LinearMap.fst k V W).comp φ.toLinearMap with hP
    set Q : (V × W) →ₗ[k] W := (LinearMap.snd k V W).comp φ.toLinearMap with hQ
    set α : V →ₗ[k] V := P.comp (LinearMap.inl k V W) with hαdef
    set β : W →ₗ[k] V := P.comp (LinearMap.inr k V W) with hβdef
    set γ : V →ₗ[k] W := Q.comp (LinearMap.inl k V W) with hγdef
    set δ : W →ₗ[k] W := Q.comp (LinearMap.inr k V W) with hδdef
    have hPvw : ∀ v w, P (v, w) = α v + β w := by
      intro v w
      have h : (v, w) = LinearMap.inl k V W v + LinearMap.inr k V W w := by
        simp
      rw [h, map_add]; rfl
    have hQvw : ∀ v w, Q (v, w) = γ v + δ w := by
      intro v w
      have h : (v, w) = LinearMap.inl k V W v + LinearMap.inr k V W w := by
        simp
      rw [h, map_add]; rfl
    have hP1 : ∀ p : V × W, (φ p : V × W).1 = P p := fun p => by simp [hP]
    have hQ2 : ∀ p : V × W, (φ p : V × W).2 = Q p := fun p => by simp [hQ]
    have hφsplit : ∀ v w, (φ (v, w) : V × W) = (P (v, w), Q (v, w)) := by
      intro v w
      exact Prod.ext (hP1 (v, w)) (hQ2 (v, w))
    -- Master intertwining identity, evaluated pointwise.
    have hmain : ∀ a v w,
        (φ (a • v + f a w, a • w) : V × W)
          = (a • P (v, w) + f' a (Q (v, w)), a • Q (v, w)) := by
      intro a v w
      have h := LinearMap.congr_fun (hφ a) (v, w)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, blockOp_apply] at h
      rw [h, hφsplit v w, blockOp_apply]
    have EfstP : ∀ a v w, P (a • v + f a w, a • w) = a • P (v, w) + f' a (Q (v, w)) := by
      intro a v w
      have h := congrArg Prod.fst (hmain a v w)
      rwa [hP1] at h
    have EsndQ : ∀ a v w, Q (a • v + f a w, a • w) = a • Q (v, w) := by
      intro a v w
      have h := congrArg Prod.snd (hmain a v w)
      rwa [hQ2] at h
    -- The four block equations.
    have hγA : ∀ (a : A) (v : V), γ (a • v) = a • γ v := by
      intro a v
      have h := EsndQ a v 0
      simpa only [map_zero, smul_zero, add_zero, hQvw] using h
    have Eq11 : ∀ (a : A) (v : V), α (a • v) = a • α v + f' a (γ v) := by
      intro a v
      have h := EfstP a v 0
      simpa only [map_zero, smul_zero, add_zero, hPvw, hQvw] using h
    have Eq12 : ∀ (a : A) (w : W), α (f a w) + β (a • w) = a • β w + f' a (δ w) := by
      intro a w
      have h := EfstP a 0 w
      simpa only [smul_zero, zero_add, hPvw, hQvw, map_zero, add_zero] using h
    have Eq22 : ∀ (a : A) (w : W), γ (f a w) + δ (a • w) = a • δ w := by
      intro a w
      have h := EsndQ a 0 w
      simpa only [smul_zero, zero_add, hQvw, map_zero, add_zero] using h
    -- Package `γ` as an `A`-linear map and apply Schur.
    let γA : V →ₗ[A] W :=
      { toFun := γ, map_add' := fun x y => γ.map_add x y, map_smul' := fun a v => hγA a v }
    rcases γA.bijective_or_eq_zero with hbij | hzero
    · -- `γ` is an isomorphism: both `f` and `f'` are coboundaries.
      let eγ : V ≃ₗ[A] W := LinearEquiv.ofBijective γA hbij
      have heγ : ∀ x, eγ x = γ x := fun x => rfl
      let gk : W →ₗ[k] V := (eγ.symm.toLinearMap).restrictScalars k
      have hgk : ∀ w, gk w = eγ.symm w := fun w => rfl
      have hγsym : ∀ w, γ (eγ.symm w) = w := by
        intro w
        have h := eγ.apply_symm_apply w
        rwa [heγ] at h
      have hfcob : f ∈ coboundaries k A V W := by
        rw [mem_coboundaries_iff]
        refine ⟨gk.comp δ, ?_⟩
        ext a w
        have hgw : γ (f a w) = a • δ w - δ (a • w) := by
          rw [eq_sub_iff_add_eq]; exact Eq22 a w
        simp only [coboundaryOf_apply, LinearMap.comp_apply, hgk]
        rw [← map_smul (eγ.symm) a (δ w), ← map_sub, ← hgw, ← heγ (f a w),
          eγ.symm_apply_apply]
      have hf'cob : f' ∈ coboundaries k A V W := by
        rw [mem_coboundaries_iff]
        refine ⟨-(α.comp gk), ?_⟩
        ext a w
        have hEq := Eq11 a (eγ.symm w)
        rw [hγsym w] at hEq
        rw [← map_smul (eγ.symm) a w] at hEq
        simp only [coboundaryOf_apply, LinearMap.neg_apply, LinearMap.comp_apply, hgk, smul_neg]
        rw [hEq]
        abel
      exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.sub_mem _ hfcob hf'cob⟩
    · -- `γ = 0`: `α`, `δ` are nonzero scalars; the `(1,2)` block gives proportionality.
      have hγ0 : ∀ v, γ v = 0 := fun v => LinearMap.congr_fun hzero v
      have hαA : ∀ (a : A) (v : V), α (a • v) = a • α v := by
        intro a v; rw [Eq11 a v, hγ0 v, map_zero, add_zero]
      have hδA : ∀ (a : A) (w : W), δ (a • w) = a • δ w := by
        intro a w
        have h := Eq22 a w
        rwa [hγ0 (f a w), zero_add] at h
      let αA : V →ₗ[A] V :=
        { toFun := α, map_add' := fun x y => α.map_add x y, map_smul' := fun a v => hαA a v }
      let δA : W →ₗ[A] W :=
        { toFun := δ, map_add' := fun x y => δ.map_add x y, map_smul' := fun a w => hδA a w }
      obtain ⟨s, hs⟩ := Etingof.Corollary_2_3_10 (k := k) (A := A) (V := V) αA
      obtain ⟨t, ht⟩ := Etingof.Corollary_2_3_10 (k := k) (A := A) (V := W) δA
      have hsα : ∀ v, α v = s • v := hs
      have htδ : ∀ w, δ w = t • w := ht
      have hs0 : s ≠ 0 := by
        intro hs_eq
        haveI : Nontrivial V := IsSimpleModule.nontrivial (R := A) (M := V)
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine hv ?_
        have hz : (φ (v, 0) : V × W) = 0 := by
          rw [hφsplit v 0, hPvw, hQvw]
          simp [hsα v, hs_eq, hγ0 v]
        have h0 := φ.map_eq_zero_iff.mp hz
        simpa using congrArg Prod.fst h0
      have ht0 : t ≠ 0 := by
        intro ht_eq
        haveI : Nontrivial W := IsSimpleModule.nontrivial (R := A) (M := W)
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        refine hw ?_
        have hQzero : ∀ q : V × W, Q q = 0 := by
          intro q
          obtain ⟨qv, qw⟩ := q
          rw [hQvw]
          simp [hγ0 qv, htδ qw, ht_eq]
        have hval : (φ (φ.symm (0, w)) : V × W).2 = w := by rw [φ.apply_symm_apply]
        rw [hQ2, hQzero] at hval
        exact hval.symm
      have hcob : s • f - t • f' ∈ coboundaries k A V W := by
        rw [mem_coboundaries_iff]
        refine ⟨β, ?_⟩
        ext a w
        have h := Eq12 a w
        rw [hsα (f a w), htδ w, map_smul (f' a) t w] at h
        simp only [coboundaryOf_apply, LinearMap.sub_apply, LinearMap.smul_apply]
        exact sub_eq_sub_iff_add_eq_add.mpr h.symm
      refine ⟨s⁻¹ * t, mul_ne_zero (inv_ne_zero hs0) ht0, ?_⟩
      have hrw : f - (s⁻¹ * t) • f' = s⁻¹ • (s • f - t • f') := by
        rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [hrw]
      exact Submodule.smul_mem _ _ hcob
  · rintro ⟨c, hc, hsub⟩
    exact ext_iso_of_sub_smul_mem_coboundaries k A V W f f' c hc hsub

end Etingof.Problem3_9_1
